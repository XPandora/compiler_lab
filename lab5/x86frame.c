#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"
#include "errormsg.h"

/*Lab5: Your implementation here.*/

//varibales
static int F_wordsize = 8;

struct F_access_
{
	enum
	{
		inFrame,
		inReg
	} kind;
	union {
		int offset;		 //inFrame
		Temp_temp reg; //inReg
	} u;
};

struct F_frame_
{
	Temp_label name;
	F_accessList formals;
	F_accessList locals;

	// the number of arguments
	int argSize;
	//the number of local variables
	int length;

	//register lists for the frame
	Temp_tempList calleesaves;
	Temp_tempList callersaves;
	Temp_tempList specialregs;
};

Temp_label F_name(F_frame f)
{
	return f->name;
}

static F_access InFrame(int offset)
{
	F_access access = checked_malloc(sizeof(*access));
	access->kind = inFrame;
	access->u.offset = offset;
	return access;
}

static F_access InReg(Temp_temp reg)
{
	F_access access = checked_malloc(sizeof(*access));
	access->kind = inReg;
	access->u.reg = reg;
	return access;
}

static F_accessList makeFAccessList(U_boolList formals, int *argSize, int offset)
{
	if (formals == NULL)
	{
		return NULL;
	}

	*argSize++;

	if (formals->head)
	{
		return F_AccessList(InFrame(offset), makeFAccessList(formals->tail, argSize, offset + F_wordsize));
	}
	else
	{
		return F_AccessList(InReg(Temp_newtemp()), makeFAccessList(formals->tail, argSize, offset));
	}
}

F_frame F_newFrame(Temp_label name, U_boolList formals)
{
	F_frame frame = checked_malloc(sizeof(*frame));
	frame->name = name;
	frame->length = 0;

	frame->calleesaves = NULL;
	frame->callersaves = NULL;
	frame->specialregs = NULL;

	int *argSize = checked_malloc(sizeof(*argSize));
	frame->formals = makeFAccessList(formals, argSize, F_wordsize);
	frame->argSize = *argSize;
	/*
	while (formals)
	{
		if (formals->head)
		{
			tail = F_AccessList(InFrame(offset), tail);
			offset += F_wordsize;
		}
		else
		{
			tail = F_AccessList(InReg(Temp_newtemp()), tail);
		}

		tail = tail->tail;
		formals = formals->tail;
		frame->argSize++;
	}*/

	return frame;
}

F_accessList F_formals(F_frame f)
{
	return f->formals;
}

F_accessList F_AccessList(F_access head, F_accessList tail)
{
	F_accessList accessList = checked_malloc(sizeof(*accessList));
	accessList->head = head;
	accessList->tail = tail;
	return accessList;
}

F_access F_allocLocal(F_frame f, bool escape)
{
	F_access access;
	if (escape)
	{
		access = InFrame(f->length);
		f->length += F_wordsize;
	}
	else
	{
		access = InReg(Temp_newtemp());
	}
	return access;
}

F_frag F_StringFrag(Temp_label label, string str)
{
	F_frag frag = checked_malloc(sizeof(*frag));
	frag->kind = F_stringFrag;
	frag->u.stringg.label = label;
	frag->u.stringg.str = str;
	return frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame)
{
	F_frag frag = checked_malloc(sizeof(*frag));
	frag->kind = F_procFrag;
	frag->u.proc.body = body;
	frag->u.proc.frame = frame;
	return frag;
}

F_fragList F_FragList(F_frag head, F_fragList tail)
{
	F_fragList fragList = checked_malloc(sizeof(*fragList));
	fragList->head = head;
	fragList->tail = tail;
	return fragList;
}

Temp_temp F_FP()
{
	return Temp_newtemp();
}

Temp_temp F_SP()
{
	return Temp_newtemp();
}

Temp_temp F_RV()
{
	return Temp_newtemp();
}

Temp_temp F_PC()
{
	return Temp_newtemp();
}

T_exp F_exp(F_access access, T_exp fp)
{
	switch (access->kind)
	{
	case inReg:
	{
		return T_Temp(access->u.reg);
	}
	case inFrame:
	{
		return T_Mem(T_Binop(T_plus, T_Const(access->u.offset), fp));
	}
	default:
	{
		printf("frame: unknown access kind\n");
		assert(0);
	}
	}
}

T_exp F_externalCall(string s, T_expList args)
{
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}


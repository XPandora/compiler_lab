#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"
#include "errormsg.h"

//LAB5: you can modify anything you want.

static F_fragList fragList = NULL;
static int F_wordsize = 8;
/*
struct Tr_access_
{
	Tr_level level;
	F_access access;
};

struct Tr_accessList_
{
	Tr_access head;
	Tr_accessList tail;
};

struct Tr_level_
{
	F_frame frame;
	Tr_level parent;
};

typedef struct patchList_ *patchList;
struct patchList_
{
	Temp_label *head;
	patchList tail;
};

struct Cx
{
	patchList trues;
	patchList falses;
	T_stm stm;
};

struct Tr_exp_
{
	enum
	{
		Tr_ex,
		Tr_nx,
		Tr_cx
	} kind;
	union {
		T_exp ex;
		T_stm nx;
		struct Cx cx;
	} u;
};*/

static Tr_exp Tr_Ex(T_exp ex)
{
	Tr_exp exp = checked_malloc(sizeof(*exp));

	exp->kind = Tr_ex;
	exp->u.ex = ex;
	return exp;
}

static Tr_exp Tr_Nx(T_stm nx)
{
	Tr_exp exp = checked_malloc(sizeof(*exp));

	exp->kind = Tr_nx;
	exp->u.nx = nx;
	return exp;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm)
{
	Tr_exp exp = checked_malloc(sizeof(*exp));

	exp->kind = Tr_cx;
	exp->u.cx.trues = trues;
	exp->u.cx.falses = falses;
	exp->u.cx.stm = stm;
	return exp;
}

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label)
{
	for (; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
	if (!first)
		return second;
	for (; first->tail; first = first->tail)
		;
	first->tail = second;
	return first;
}

static T_exp unEx(Tr_exp e)
{
	switch (e->kind)
	{
	case Tr_ex:
		return e->u.ex;
	case Tr_cx:
	{
		Temp_temp r = Temp_newtemp();
		Temp_label t = Temp_newlabel(), f = Temp_newlabel();
		doPatch(e->u.cx.trues, t);
		doPatch(e->u.cx.falses, f);
		return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
									T_Eseq(e->u.cx.stm,
												 T_Eseq(T_Label(f),
																T_Eseq(T_Move(T_Temp(r), T_Const(0)),
																			 T_Eseq(T_Label(t), T_Temp(r))))));
	}
	case Tr_nx:
		return T_Eseq(e->u.nx, T_Const(0));
	}
	assert(0);
}

static T_stm unNx(Tr_exp e)
{
	switch (e->kind)
	{
	case Tr_ex:
	{
		return T_Exp(e->u.ex);
	}
	case Tr_cx:
	{
		return e->u.nx;
	}
	case Tr_nx:
	{
		return T_Exp(unEx(e));
	}
	}
	assert(0);
}

static struct Cx unCx(Tr_exp e)
{

	switch (e->kind)
	{
	case Tr_ex:
	{
		// optimization?
		// Treat the cases of CONST 0 and CONST 1 specially
		struct Cx cx;
		T_stm s = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
		patchList trues = PatchList(&(s->u.CJUMP.true), NULL);
		patchList falses = PatchList(&(s->u.CJUMP.false), NULL);

		cx.stm = s;
		cx.trues = trues;
		cx.falses = falses;

		return cx;
	}
	case Tr_cx:
	{
		return e->u.cx;
	}
	case Tr_nx:
	{
		printf("can not unCx a Tr_nx type\n");
		assert(0);
	}
	}
	assert(0);
}

static Tr_accessList makeTrAccessList(F_accessList accessList, Tr_level level)
{
	if (accessList)
	{
		Tr_access tr_access = checked_malloc(sizeof(*tr_access));
		tr_access->level = level;
		tr_access->access = accessList->head;

		return Tr_AccessList(tr_access, makeTrAccessList(accessList->tail, level));
	}
	else
	{
		return NULL;
	}
}

static T_expList makeTExpList(Tr_expList params)
{
	if (params)
	{
		return T_ExpList(unEx(params->head), makeTExpList(params->tail));
	}
	else
	{
		return NULL;
	}
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail)
{
	Tr_expList expList = checked_malloc(sizeof(*expList));
	expList->head = head;
	expList->tail = tail;
	return expList;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
	Tr_accessList accessList = checked_malloc(sizeof(*accessList));
	accessList->head = head;
	accessList->tail = tail;
	return accessList;
}

Tr_level Tr_outermost(void)
{
	// static?
	Tr_level outermost = checked_malloc(sizeof(*outermost));

	Temp_label label = Temp_newlabel();
	outermost->frame = F_newFrame(label, NULL);
	outermost->parent = NULL;
	return outermost;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
	Tr_level level = checked_malloc(sizeof(*level));
	level->parent = parent;
	level->frame = F_newFrame(name, U_BoolList(TRUE, formals));
	return level;
}

Tr_accessList Tr_formals(Tr_level level)
{
	// ->tail for skipping static link
	return makeTrAccessList(F_formals(level->frame)->tail, level);
}

Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
	Tr_access tr_access = checked_malloc(sizeof(*tr_access));
	tr_access->level = level;
	tr_access->access = F_allocLocal(level->frame, escape);
	return tr_access;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)
{
	T_exp access_fp = T_Temp(F_FP());
	while (access->level != level)
	{
		access_fp = T_Mem(T_Binop(T_plus, access_fp, T_Const(F_wordsize)));
		level = level->parent;
	}
	return Tr_Ex(F_exp(access->access, access_fp));
}

Tr_exp Tr_fieldVar(Tr_exp addr, int n)
{
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(addr), T_Const(n * F_wordsize))));
}

Tr_exp Tr_subscriptVar(Tr_exp addr, Tr_exp index)
{
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(addr), T_Binop(T_mul, T_Const(F_wordsize), unEx(index)))));
}
Tr_exp Tr_nil()
{
	return Tr_Ex(T_Const(0));
}

Tr_exp Tr_int(int value)
{
	return Tr_Ex(T_Const(value));
}

Tr_exp Tr_string(string str)
{
	Temp_label label = Temp_newlabel();
	F_frag frag = F_StringFrag(label, str);

	fragList = F_FragList(frag, fragList);
	return Tr_Ex(T_Name(label));
}

Tr_exp Tr_call(Tr_level caller, Temp_label label, Tr_expList params, Tr_level callee)
{
	T_exp staticlink = T_Temp(F_FP());

	while (caller != callee->parent)
	{
		staticlink = T_Mem(T_Binop(T_plus, staticlink, T_Const(F_wordsize)));
		caller = caller->parent;
	}

	T_expList t_params = makeTExpList(params);
	return Tr_Ex(T_Call(T_Name(label), T_ExpList(staticlink, t_params)));
}

Tr_exp Tr_arith(A_oper oper, Tr_exp left, Tr_exp right)
{
	switch (oper)
	{
	case A_plusOp:
	{
		return Tr_Ex(T_Binop(T_plus, unEx(left), unEx(right)));
	}
	case A_minusOp:
	{
		return Tr_Ex(T_Binop(T_minus, unEx(left), unEx(right)));
	}
	case A_timesOp:
	{
		return Tr_Ex(T_Binop(T_mul, unEx(left), unEx(right)));
	}
	case A_divideOp:
	{
		return Tr_Ex(T_Binop(T_div, unEx(left), unEx(right)));
	}
	default:
	{
		printf("translate: in arith unexpected oper %d", oper);
		return Tr_Ex(T_Const(0));
	}
	}
}

Tr_exp Tr_condition(A_oper oper, Tr_exp left, Tr_exp right)
{
	T_stm s;
	switch (oper)
	{
	case A_eqOp:
	{
		s = T_Cjump(T_eq, unEx(left), unEx(right), NULL, NULL);
		break;
	}
	case A_neqOp:
	{
		s = T_Cjump(T_ne, unEx(left), unEx(right), NULL, NULL);
		break;
	}
	case A_gtOp:
	{
		s = T_Cjump(T_gt, unEx(left), unEx(right), NULL, NULL);
		break;
	}
	case A_geOp:
	{
		s = T_Cjump(T_ge, unEx(left), unEx(right), NULL, NULL);
		break;
	}
	case A_ltOp:
	{
		s = T_Cjump(T_lt, unEx(left), unEx(right), NULL, NULL);
		break;
	}
	case A_leOp:
	{
		s = T_Cjump(T_le, unEx(left), unEx(right), NULL, NULL);
		break;
	}
	default:
	{
		printf("translate: in condition unexpected oper %d", oper);
		s = T_Cjump(T_eq, unEx(left), unEx(right), NULL, NULL);
	}
	}

	patchList trues = PatchList(&s->u.CJUMP.true, NULL);
	patchList falses = PatchList(&s->u.CJUMP.false, NULL);

	return Tr_Cx(trues, falses, s);
}

Tr_exp Tr_record(Tr_expList fields)
{
	int fields_count = 0;

	Tr_expList temp_fields = fields;
	while (temp_fields)
	{
		temp_fields = temp_fields->tail;
		fields_count++;
	}

	Temp_temp record_addr = Temp_newtemp();
	T_exp addr = F_externalCall("malloc", T_ExpList(T_Binop(T_mul, T_Const(F_wordsize), T_Const(fields_count)), NULL));

	T_stm s = T_Move(T_Temp(record_addr), addr);

	for (int i = 0; fields; i++, fields = fields->tail)
	{
		T_stm stm = T_Move(T_Binop(T_plus, T_Temp(record_addr), T_Binop(T_mul, T_Const(i), T_Const(F_wordsize))),
											 unEx(fields->head));
		s = T_Seq(s, stm);
	}

	return Tr_Ex(T_Eseq(s, T_Temp(record_addr)));
}

Tr_exp Tr_seq(Tr_exp first, Tr_exp second)
{
	return Tr_Ex(T_Eseq(unNx(first), unEx(second)));
}

Tr_exp Tr_ifthenelse(Tr_exp test, Tr_exp then, Tr_exp elsee)
{
	// result temp
	Temp_temp result = Temp_newtemp();

	// finish label
	Temp_label finish_label = Temp_newlabel();
	T_exp finish_exp = T_Eseq(T_Label(finish_label), T_Temp(result));

	Temp_label t_label = Temp_newlabel();
	T_stm t_stm = T_Seq(T_Move(T_Temp(result), unEx(then)),
											T_Jump(T_Name(finish_label), Temp_LabelList(finish_label, NULL)));
	t_stm = T_Seq(T_Label(t_label), t_stm);

	Temp_label f_label = Temp_newlabel();
	T_stm f_stm = T_Seq(T_Move(T_Temp(result), unEx(elsee)),
											T_Jump(T_Name(finish_label), Temp_LabelList(finish_label, NULL)));
	f_stm = T_Seq(T_Label(f_label), f_stm);

	struct Cx cx = unCx(test);
	doPatch(cx.trues, t_label);
	doPatch(cx.falses, f_label);

	return Tr_Ex(T_Eseq(T_Seq(cx.stm, T_Seq(t_stm, f_stm)), finish_exp));
}

Tr_exp Tr_array(Tr_exp size, Tr_exp init)
{
	Temp_temp array_addr = Temp_newtemp();

	T_stm s = T_Move(T_Temp(array_addr), F_externalCall("initArray",
																											T_ExpList(unEx(size), T_ExpList(unEx(init), NULL))));

	return Tr_Ex(T_Eseq(s, T_Temp(array_addr)));
}

Tr_exp Tr_assign(Tr_exp lvalue, Tr_exp value)
{
	return Tr_Nx(T_Move(unEx(lvalue), unEx(value)));
}

Tr_exp Tr_while(Tr_exp test, Tr_exp body, Temp_label done)
{
	Temp_label test_label = Temp_newlabel();
	Temp_label body_label = Temp_newlabel();

	struct Cx cx = unCx(test);
	doPatch(cx.trues, body_label);
	doPatch(cx.falses, done);

	T_stm test_stm = T_Seq(T_Label(test_label), cx.stm);
	T_stm body_stm = T_Seq(T_Label(body_label),
												 T_Seq(unNx(body), T_Jump(T_Name(test_label), Temp_LabelList(test_label, NULL))));

	return Tr_Nx(T_Seq(test_stm, T_Seq(body_stm, T_Label(done))));
}

Tr_exp Tr_for(Tr_access access, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done)
{
	// init var
	T_exp hi_exp = T_Temp(Temp_newtemp());
	T_exp loop_var = F_exp(access->access, T_Temp(F_FP()));
	T_stm init_stm = T_Seq(T_Move(loop_var, unEx(lo)), T_Move(hi_exp, unEx(hi)));

	// test stm
	Temp_label test_label = Temp_newlabel();
	Temp_label body_label = Temp_newlabel();

	T_stm test_stm = T_Seq(T_Label(test_label),
												 T_Cjump(T_le, loop_var, hi_exp, body_label, done));

	// body stm
	T_stm increse_stm = T_Move(loop_var, T_Binop(T_plus, loop_var, T_Const(1)));
	T_stm body_stm = T_Seq(T_Label(body_label),
												 T_Seq(unNx(body),
															 T_Seq(increse_stm,
																		 T_Jump(T_Name(test_label), Temp_LabelList(test_label, NULL)))));

	return Tr_Nx(T_Seq(init_stm, T_Seq(test_stm, T_Seq(body_stm, T_Label(done)))));
}

Tr_exp Tr_break(Temp_label done)
{
	return Tr_Nx(T_Jump(T_Name(done), Temp_LabelList(done, NULL)));
}

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals)
{
	// something else...
	T_stm s = T_Move(T_Temp(F_RV()), unEx(body));

	F_frag frag = F_ProcFrag(s, level->frame);
	fragList = F_FragList(frag, fragList);
}

F_fragList Tr_getResult(void)
{
	return fragList;
}


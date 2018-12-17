#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"

/*Lab4: Your implementation of lab4*/

typedef void *Tr_exp;
struct expty
{
	Tr_exp exp;
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty actual_ty(Ty_ty ty)
{
	while (ty && ty->kind == Ty_name)
	{
		ty = ty->u.name.ty;
	}

	return ty;
}

Ty_tyList makeFomalTyList(S_table tenv, A_fieldList fields)
{
	if (fields == NULL)
	{
		return NULL;
	}

	Ty_ty head_ty = S_look(tenv, fields->head->typ);
	if (head_ty == NULL)
	{
		EM_error(fields->head->pos, "undefined type %s", S_name(fields->head->typ));
		head_ty = Ty_Int();
	}
	Ty_tyList next = makeFomalTyList(tenv, fields->tail);

	return Ty_TyList(head_ty, next);
}

Ty_fieldList makeRecordTyList(S_table tenv, A_fieldList fields)
{
	if (fields == NULL)
	{
		return NULL;
	}

	Ty_ty head_ty = S_look(tenv, fields->head->typ);
	if (head_ty == NULL)
	{
		EM_error(fields->head->pos, "undefined type %s", S_name(fields->head->typ));
		head_ty = Ty_Int();
	}
	Ty_field head_field = Ty_Field(fields->head->name, head_ty);
	Ty_fieldList next = makeRecordTyList(tenv, fields->tail);

	return Ty_FieldList(head_field, next);
}

struct expty transVar(S_table venv, S_table tenv, A_var v)
{
	switch (v->kind)
	{
	case A_simpleVar:
	{
		E_enventry x = S_look(venv, v->u.simple);
		if (x && x->kind == E_varEntry)
		{
			return expTy(NULL, actual_ty(x->u.var.ty));
		}
		else
		{
			EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
			return expTy(NULL, Ty_Int());
		}
	}
	case A_fieldVar:
	{
		struct expty varty = transVar(venv, tenv, v->u.field.var);

		if (varty.ty->kind != Ty_record)
		{
			EM_error(v->pos, "not a record type");
			return expTy(NULL, Ty_Int());
		}

		Ty_fieldList record = varty.ty->u.record;
		while (record)
		{
			if (record->head->name == v->u.field.sym)
			{
				return expTy(NULL, actual_ty(record->head->ty));
			}

			record = record->tail;
		}

		EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
		return expTy(NULL, Ty_Int());
	}
	case A_subscriptVar:
	{
			struct expty varty = transVar(venv, tenv, v->u.subscript.var);

			if (varty.ty->kind != Ty_array)
			{
				EM_error(v->pos, "array type required");
				return expTy(NULL, Ty_Int());
			}

			struct expty expty = transExp(venv, tenv, v->u.subscript.exp);

			if (expty.ty->kind != Ty_int)
			{
				EM_error(v->u.subscript.exp->pos, "type should be int");
				return expTy(NULL, Ty_Int());
			}

			return expTy(NULL, actual_ty(varty.ty->u.array));
	}
	}
	assert(0);
}

struct expty transExp(S_table venv, S_table tenv, A_exp a)
{
	switch (a->kind)
	{
	case A_varExp:
	{
		return transVar(venv, tenv, a->u.var);
	}
	case A_nilExp:
	{
		return expTy(NULL, Ty_Nil());
	}
	case A_intExp:
	{
		return expTy(NULL, Ty_Int());
	}
	case A_stringExp:
	{
		return expTy(NULL, Ty_String());
	}
	case A_callExp:
	{
		E_enventry x = S_look(venv, a->u.call.func);
		if ((x == NULL) || (x->kind != E_funEntry))
		{
			EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
			return expTy(NULL, Ty_Int());
		}

		A_expList args = a->u.call.args;
		Ty_tyList formals = x->u.fun.formals;
		Ty_ty result = x->u.fun.result;

		while (args && formals)
		{
			struct expty arg = transExp(venv, tenv, args->head);
			Ty_ty formal = formals->head;

			if (actual_ty(arg.ty)->kind != actual_ty(formal)->kind)
			{
				EM_error(args->head->pos, "para type mismatch");
			}

			args = args->tail;
			formals = formals->tail;
		}

		if (args != NULL)
		{
			EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
		}
		if (formals != NULL)
		{
			EM_error(a->pos, "too few params in function %s", S_name(a->u.call.func));
		}

		return expTy(NULL, actual_ty(result));
	}
	case A_opExp:
	{
		A_oper oper = a->u.op.oper;
		struct expty left = transExp(venv, tenv, a->u.op.left);
		struct expty right = transExp(venv, tenv, a->u.op.right);
		if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp)
		{
			if (actual_ty(left.ty)->kind != Ty_int)
			{
				EM_error(a->u.op.left->pos, "integer required");
			}
			if (actual_ty(right.ty)->kind != Ty_int)
			{
				EM_error(a->u.op.right->pos, "integer required");
			}
		}
		else
		{
			if (actual_ty(left.ty) != actual_ty(right.ty))
			{
				EM_error(a->u.op.left->pos, "same type required");
			}
		}
		return expTy(NULL, Ty_Int());
	}
	case A_recordExp:
	{
		Ty_ty recordty = S_look(tenv, a->u.record.typ);
		recordty = actual_ty(recordty);

		if ((recordty == NULL) || (recordty->kind != Ty_record))
		{
			EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
			return expTy(NULL, Ty_Int());
		}

		A_efieldList fields = a->u.record.fields;
		Ty_fieldList records = recordty->u.record;
		while (fields && records)
		{
			A_efield efield = fields->head;
			Ty_field field = records->head;

			if (field->name != efield->name)
			{
				EM_error(a->pos, "type name %s does not match", S_name(efield->name));
				return expTy(NULL, Ty_Int());
			}

			struct expty actual = transExp(venv, tenv, efield->exp);
			if (actual_ty(actual.ty) != actual_ty(field->ty))
			{
				EM_error(a->pos, "actual type does not match");
				return expTy(NULL, Ty_Int());
			}

			fields = fields->tail;
			records = records->tail;
		}

		if ((fields != NULL) || (records != NULL))
		{
			EM_error(a->pos, "type num does not match");
			return expTy(NULL, Ty_Int());
		}

		return expTy(NULL, recordty);
	}
	case A_seqExp:
	{
		A_expList seq = a->u.seq;
		struct expty result = expTy(NULL, Ty_Void());

		while (seq)
		{
			result = transExp(venv, tenv, seq->head);
			seq = seq->tail;
		}

		return result;
	}
	case A_assignExp:
	{
		A_var assign_var = a->u.assign.var;
		A_exp assign_exp = a->u.assign.exp;

		if (assign_var->kind == A_simpleVar)
		{
			E_enventry x = S_look(venv, assign_var->u.simple);
			if (x->u.var.ROFlag)
			{
				EM_error(assign_var->pos, "loop variable can't be assigned");
				return expTy(NULL, Ty_Void());
			}
		}

		struct expty assign_exp_ty = transExp(venv, tenv, assign_exp);
		struct expty assign_var_ty = transVar(venv, tenv, assign_var);

		if (actual_ty(assign_exp_ty.ty) != actual_ty(assign_var_ty.ty))
		{
			EM_error(a->pos, "unmatched assign exp");
			return expTy(NULL, Ty_Void());
		}

		return expTy(NULL, Ty_Void());
	}
	case A_ifExp:
	{
		A_exp test = a->u.iff.test;
		A_exp then = a->u.iff.then;
		A_exp elsee = a->u.iff.elsee;

		struct expty test_ty = transExp(venv, tenv, test);

		if (actual_ty(test_ty.ty)->kind != Ty_int)
		{
			EM_error(test->pos, "if test type error");
			return expTy(NULL, Ty_Int());
		}

		struct expty then_ty = transExp(venv, tenv, then);

		if ((elsee != NULL) && (elsee->kind != A_nilExp))
		{
			struct expty elsee_ty = transExp(venv, tenv, elsee);
			if (actual_ty(then_ty.ty) != actual_ty(elsee_ty.ty))
			{
				EM_error(then->pos, "then exp and else exp type mismatch");
				return expTy(NULL, Ty_Int());
			}
		}
		else
		{
			if (actual_ty(then_ty.ty)->kind != Ty_void)
			{
				EM_error(then->pos, "if-then exp's body must produce no value");
			}
		}

		return expTy(NULL, actual_ty(then_ty.ty));
	}
	case A_whileExp:
	{
		A_exp test = a->u.whilee.test;
		A_exp body = a->u.whilee.body;

		struct expty test_ty = transExp(venv, tenv, test);
		struct expty body_ty = transExp(venv, tenv, body);

		if (actual_ty(test_ty.ty)->kind != Ty_int)
		{
			EM_error(test->pos, "while test type should be int");
		}

		if (actual_ty(body_ty.ty)->kind != Ty_void)
		{
			EM_error(body->pos, "while body must produce no value");
		}

		return expTy(NULL, Ty_Void());
	}
	case A_forExp:
	{
		A_exp lo = a->u.forr.lo;
		A_exp hi = a->u.forr.hi;
		A_exp body = a->u.forr.body;
		struct expty lo_ty = transExp(venv, tenv, lo);
		struct expty hi_ty = transExp(venv, tenv, hi);

		if ((actual_ty(lo_ty.ty)->kind != Ty_int) || (actual_ty(hi_ty.ty)->kind != Ty_int))
		{
			EM_error(lo->pos, "for exp's range type is not integer");
		}

		S_beginScope(venv);
		S_enter(venv, a->u.forr.var, E_ROVarEntry(Ty_Int()));
		struct expty body_ty = transExp(venv, tenv, body);
		S_endScope(venv);

		if (actual_ty(body_ty.ty)->kind != Ty_void)
		{
			EM_error(body->pos, "for body type should be void");
		}

		return expTy(NULL, Ty_Void());
	}
	case A_breakExp:
	{
		return expTy(NULL, Ty_Void());
	}
	case A_letExp:
	{
		struct expty letexp;
		A_decList d;
		S_beginScope(venv);
		S_beginScope(tenv);
		for (d = a->u.let.decs; d; d = d->tail)
		{
			transDec(venv, tenv, d->head);
		}
		letexp = transExp(venv, tenv, a->u.let.body);
		S_endScope(tenv);
		S_endScope(venv);
		return letexp;
	}
	case A_arrayExp:
	{
		Ty_ty array_ty = S_look(tenv, a->u.array.typ);
		array_ty = actual_ty(array_ty);
		if (array_ty == NULL || array_ty->kind != Ty_array)
		{
			EM_error(a->pos, "undefined array %s", S_name(a->u.array.typ));
			return expTy(NULL, Ty_Int());
		}

		A_exp size = a->u.array.size;
		A_exp init = a->u.array.init;

		struct expty size_ty = transExp(venv, tenv, size);
		struct expty init_ty = transExp(venv, tenv, init);

		if (actual_ty(size_ty.ty)->kind != Ty_int)
		{
			EM_error(size->pos, "array size type should be int");
		}

		if (actual_ty(init_ty.ty) != actual_ty(array_ty->u.array))
		{
			EM_error(init->pos, "type mismatch");
		}

		return expTy(NULL, array_ty);
	}
	}
	assert(0);
}

void transDec(S_table venv, S_table tenv, A_dec d)
{
	switch (d->kind)
	{
	case A_functionDec:
	{
		A_fundecList fundeclist = d->u.function;

		// head
		while (fundeclist)
		{
			A_fundec f = fundeclist->head;
			Ty_ty resultTy = Ty_Void();

			if (S_look(venv, f->name) != NULL)
			{
				EM_error(f->pos, "two functions have the same name");
				fundeclist = fundeclist->tail;
				continue;
			}

			if (f->result != NULL)
			{
				resultTy = S_look(tenv, f->result);
			}

			if (resultTy == NULL)
			{
				EM_error(f->pos, "undefined function return type %s", S_name(f->result));
				resultTy = Ty_Void();
			}

			Ty_tyList formalTys = makeFomalTyList(tenv, f->params);
			S_enter(venv, f->name, E_FunEntry(formalTys, resultTy));

			fundeclist = fundeclist->tail;
		}

		// body
		fundeclist = d->u.function;
		while (fundeclist)
		{
			A_fundec f = fundeclist->head;
			A_fieldList fields = f->params;
			Ty_tyList formalTys = makeFomalTyList(tenv, f->params);
			S_beginScope(venv);
			while (fields != NULL && formalTys != NULL)
			{
				Ty_ty formal = formalTys->head;
				A_field field = fields->head;
				S_enter(venv, field->name, E_VarEntry(formal));

				fields = fields->tail;
				formalTys = formalTys->tail;
			}

			struct expty e = transExp(venv, tenv, f->body);

			E_enventry x = S_look(venv, f->name);
			Ty_ty resultTy = x->u.fun.result;

			if (actual_ty(resultTy) != actual_ty(e.ty))
			{
				if (actual_ty(resultTy)->kind == Ty_void)
				{
					EM_error(f->pos, "procedure returns value");
				}
				else
				{
					if (!(actual_ty(resultTy)->kind == Ty_record && actual_ty(e.ty)->kind == Ty_nil))
					{
						EM_error(f->pos, "function return type does not match");
					}
				}
			}
			S_endScope(venv);
			fundeclist = fundeclist->tail;
		}

		break;
	}
	case A_varDec:
	{
		struct expty e = transExp(venv, tenv, d->u.var.init);

		if (d->u.var.typ != NULL)
		{
			Ty_ty var_ty = S_look(tenv, d->u.var.typ);

			if (var_ty == NULL)
			{
				EM_error(d->pos, "undefined type %s", S_name(d->u.var.typ));
				return;
			}

			if (actual_ty(var_ty)->kind == Ty_record)
			{
				if (actual_ty(e.ty) == actual_ty(var_ty) || actual_ty(e.ty)->kind == Ty_nil)
				{
					S_enter(venv, d->u.var.var, E_VarEntry(var_ty));
					return;
				}

				EM_error(d->pos, "type mismatch");
			}
			else
			{
				if (actual_ty(var_ty) == actual_ty(e.ty))
				{
					S_enter(venv, d->u.var.var, E_VarEntry(var_ty));
					return;
				}

				EM_error(d->pos, "type mismatch");
			}
		}
		else
		{
			if (actual_ty(e.ty)->kind == Ty_nil)
			{
				EM_error(d->u.var.init->pos, "init should not be nil without type specified");
			}
		}
		S_enter(venv, d->u.var.var, E_VarEntry(e.ty));
		break;
	}
	case A_typeDec:
	{
		A_nametyList typelist = d->u.type;

		// head
		while (typelist)
		{
			A_namety t = typelist->head;
			if (S_look(tenv, t->name) != NULL)
			{
				EM_error(d->pos, "two types have the same name");
			}
			else
			{
				S_enter(tenv, t->name, Ty_Name(t->name, NULL));
			}

			typelist = typelist->tail;
		}

		// body
		typelist = d->u.type;
		while (typelist)
		{
			A_namety t = typelist->head;
			Ty_ty ty = S_look(tenv, t->name);
			ty->u.name.ty = transTy(tenv, t->ty);

			typelist = typelist->tail;
		}

		// check cycle
		typelist = d->u.type;
		while (typelist)
		{
			A_namety n = typelist->head;
			Ty_ty i = S_look(tenv, n->name);
			Ty_ty t = i;
			t = t->u.name.ty;

			while (t->kind == Ty_name)
			{
				if (t->u.name.sym == n->name)
				{
					EM_error(d->pos, "illegal type cycle");
					i->u.name.ty = Ty_Void();
					break;
				}
				t = t->u.name.ty;
			}

			typelist = typelist->tail;
		}
		break;
	}
	}
}

Ty_ty transTy(S_table tenv, A_ty a)
{
	switch (a->kind)
	{
	case A_nameTy:
	{
		Ty_ty t = S_look(tenv, a->u.name);
		if (t == NULL)
		{
			EM_error(a->pos, "undefined type %s", S_name(a->u.name));
			return Ty_Int();
		}
		return Ty_Name(a->u.name, t);
	}
	case A_recordTy:
	{
		A_fieldList record = a->u.record;
		return Ty_Record(makeRecordTyList(tenv, record));
	}
	case A_arrayTy:
	{
		Ty_ty t = S_look(tenv, a->u.array);
		if (t == NULL)
		{
			EM_error(a->pos, "undefined type %s", S_name(a->u.array));
			return Ty_Int();
		}
		return Ty_Array(t);
	}
	}
	assert(0);
}

void SEM_transProg(A_exp exp)
{
	transExp(E_base_venv(), E_base_tenv(), exp);
}

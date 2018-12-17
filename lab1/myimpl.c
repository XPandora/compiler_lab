#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "prog1.h"

typedef struct table *Table_t;
typedef struct IntAndTable *IntAndTable_t;

struct table
{
	string id;
	int value;
	Table_t tail;
};

struct IntAndTable
{
	int value;
	Table_t t;
};

int max(int a, int b);
int args_in_expList(A_expList expList);
int maxargs_expList(A_expList expList);
int maxargs_exp(A_exp exp);
Table_t getTable(string id, int value, Table_t tail);
Table_t interpStm(A_stm stm, Table_t table);
int lookup(Table_t t, string key);
IntAndTable_t getIntAndTable(int value, Table_t table);
IntAndTable_t interpExp(A_exp exp, Table_t table);
IntAndTable_t interpExpList(A_expList expList, Table_t table);

int maxargs(A_stm stm)
{
	if (stm->kind == A_assignStm)
	{
		A_exp exp = stm->u.assign.exp;
		return maxargs_exp(exp);
	}

	else if (stm->kind == A_printStm)
	{
		A_expList expList = stm->u.print.exps;
		return max(args_in_expList(expList), maxargs_expList(expList));
	}

	else if (stm->kind == A_compoundStm)
	{
		A_stm stm1 = stm->u.compound.stm1;
		A_stm stm2 = stm->u.compound.stm2;
		return max(maxargs(stm1), maxargs(stm2));
	}
	else
	{
		assert(FALSE);
	}

	return 0;
}

void interp(A_stm stm)
{
	interpStm(stm, NULL);
}

int max(int a, int b)
{
	return a > b ? a : b;
}

int args_in_expList(A_expList expList)
{
	if (expList->kind == A_lastExpList)
	{
		return 1;
	}
	else if (expList->kind == A_pairExpList)
	{
		return 1 + args_in_expList(expList->u.pair.tail);
	}
	else
	{
		assert(FALSE);
	}
}

int maxargs_expList(A_expList expList)
{
	if (expList->kind == A_lastExpList)
	{
		return max(maxargs_exp(expList->u.last), 1);
	}
	else if (expList->kind == A_pairExpList)
	{
		return max(maxargs_exp(expList->u.pair.head), maxargs_expList(expList->u.pair.tail));
	}
	else
	{
		assert(FALSE);
	}
}

int maxargs_exp(A_exp exp)
{
	if (exp->kind == A_idExp || exp->kind == A_numExp)
	{
		return 0;
	}
	else if (exp->kind == A_opExp)
	{
		A_exp exp1 = exp->u.op.left;
		A_exp exp2 = exp->u.op.right;
		return max(maxargs_exp(exp1), maxargs_exp(exp2));
	}
	else if (exp->kind == A_eseqExp)
	{
		A_stm stm1 = exp->u.eseq.stm;
		A_exp exp1 = exp->u.eseq.exp;
		return max(maxargs(stm1), maxargs_exp(exp1));
	}
	else
	{
		assert(FALSE);
	}
}

Table_t getTable(string id, int value, Table_t tail)
{
	Table_t t = malloc(sizeof(*t));
	t->id = id;
	t->value = value;
	t->tail = tail;
	return t;
}

Table_t interpStm(A_stm stm, Table_t table)
{
	if (stm->kind == A_compoundStm)
	{
		A_stm stm1 = stm->u.compound.stm1;
		A_stm stm2 = stm->u.compound.stm2;
		Table_t table1 = interpStm(stm1, table);
		Table_t table2 = interpStm(stm2, table1);
		return table2;
	}
	else if (stm->kind == A_assignStm)
	{
		string id = stm->u.assign.id;
		A_exp exp = stm->u.assign.exp;
		IntAndTable_t intTable = interpExp(exp, table);
		return getTable(id, intTable->value, intTable->t);
	}
	else if (stm->kind == A_printStm)
	{
		IntAndTable_t intTable = interpExpList(stm->u.print.exps,table);
		return intTable->t;
	}
	else
	{
		assert(FALSE);
	}
}

int lookup(Table_t t, string key)
{
	if (t == NULL)
	{
		assert(FALSE);
	}

	if (key == t->id)
	{
		return t->value;
	}
	return lookup(t->tail, key);
}

IntAndTable_t getIntAndTable(int value, Table_t table)
{
	IntAndTable_t intTable = malloc(sizeof(*intTable));
	intTable->value = value;
	intTable->t = table;
	return intTable;
}

IntAndTable_t interpExp(A_exp exp, Table_t table)
{
	if (exp->kind == A_idExp)
	{
		return getIntAndTable(lookup(table, exp->u.id), table);
	}
	else if (exp->kind == A_numExp)
	{
		return getIntAndTable(exp->u.num, table);
	}
	else if (exp->kind == A_opExp)
	{
		IntAndTable_t intTable1 = interpExp(exp->u.op.left, table);
		IntAndTable_t intTable2 = interpExp(exp->u.op.right, intTable1->t);

		switch (exp->u.op.oper)
		{
		case A_plus:
			return getIntAndTable(intTable1->value + intTable2->value, intTable2->t);
		case A_minus:
			return getIntAndTable(intTable1->value - intTable2->value, intTable2->t);
		case A_times:
			return getIntAndTable(intTable1->value * intTable2->value, intTable2->t);
		case A_div:
			return getIntAndTable(intTable1->value / intTable2->value, intTable2->t);
		default:
			assert(FALSE);
		}
	}
	else if (exp->kind == A_eseqExp)
	{
		Table_t table1 = interpStm(exp->u.eseq.stm, table);
		return interpExp(exp->u.eseq.exp, table1);
	}
	else
	{
		assert(FALSE);
	}
}

IntAndTable_t interpExpList(A_expList expList, Table_t table)
{
	if (expList->kind == A_lastExpList)
	{
		IntAndTable_t intTable = interpExp(expList->u.last, table);
		printf("%d\n", intTable->value);
		return intTable;
	}
	else if (expList->kind == A_pairExpList)
	{
		IntAndTable_t intTable = interpExp(expList->u.pair.head, table);
		printf("%d ", intTable->value);
		return interpExpList(expList->u.pair.tail, intTable->t);
	}
}

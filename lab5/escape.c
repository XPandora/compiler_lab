#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "escape.h"

E_escapeEntry E_EscapeEntry(int depth, bool *escape)
{
  E_escapeEntry entry = checked_malloc(sizeof(*entry));
  entry->depth = depth;
  entry->escape = escape;
  return entry;
}

static void traverseExp(S_table env, int depth, A_exp e)
{
  switch (e->kind)
  {
  case A_varExp:
  {
    return transVar(env, depth, e->u.var);
  }
  case A_nilExp:
  case A_intExp:
  case A_stringExp:
  {
    return;
  }
  case A_callExp:
  {
    A_expList args = e->u.call.args;

    while (args)
    {
      traverseExp(env, depth, args->head);
      args = args->tail;
    }
    return;
  }
  case A_opExp:
  {
    traverseExp(env, depth, e->u.op.left);
    traverseExp(env, depth, e->u.op.right);
    return;
  }
  case A_recordExp:
  {
    A_efieldList fields = e->u.record.fields;

    while (fields)
    {
      traverseExp(env, depth, fields->exp);
      fields = fields->tail;
    }
    return;
  }
  case A_seqExp:
  {
    A_expList seq = e->u.seq;

    while (seq)
    {
      traverseExp(env, depth, seq->head);
      seq = seq->tail;
    }
    return;
  }
  case A_assignExp:
  {
    traverseExp(env, depth, e->u.assign.exp);
    traverseVar(env, depth, e->u.assign.var);
    return;
  }
  case A_ifExp:
  {
    traverseExp(env, depth, e->u.iff.test);
    traverseExp(env, depth, e->u.iff.then);
    traverseExp(env, depth, e->u.iff.elsee);
    return;
  }
  case A_whileExp:
  {
    traverseExp(env, depth, e->u.whilee.test);
    traverseExp(env, depth, e->u.whilee.body);
    return;
  }
  case A_forExp:
  {
    traverseExp(env, depth, e->u.forr.lo);
    traverseExp(env, depth, e->u.forr.hi);

    S_beginScope(env);
    S_enter(env, e->u.forr.var, E_EscapeEntry(depth, &(e->u.forr.escape)));
    traverseExp(env, depth, e->u.forr.body);
    S_endScope(env);

    return;
  }
  case A_breakExp:
  {
    return;
  }
  case A_letExp:
  {
    A_decList d;
    S_beginScope(env);
    for (d = e->let.decs; d; d = d->tail)
    {
      traverseDec(env, depth, d->head);
    }

    traverseExp(env, depth, e->u.let.body);
    S_endScope(env);
    return;
  }
  case A_arrayExp:
  {
    traverseExp(env, depth, e->u.array.size);
    traverseExp(env, depth, e->u.array.init);
    return;
  }
  }
  assert(0);
}

static void traverseDec(S_table env, int depth, A_dec d)
{
  switch (d->kind)
  {
  case A_functionDec:
  {
    A_fundecList fundeclist = d->u.function;

    while (fundeclist)
    {
      A_fundec f = fundeclist->head;
      A_fieldList params = f->params;
      S_beginScope(env);

      while (params)
      {
        S_enter(env, params->head->name, E_EscapeEntry(depth + 1, &(params->head->escape)));
        params->head->escape = FALSE;
        params = params->tail;
      }
      traverseExp(env, depth + 1, f->body);
      S_endScope(env);
      fundeclist = fundeclist->tail;
    }

    return;
  }
  case A_varDec:
  {
    traverseExp(env, depth, d->u.var.init);
    S_enter(env, d->u.var.var, E_EscapeEntry(depth, &(d->u.var.escape)));
    d->u.var.escape = 0;
    return;
  }
  case A_typeDec:
  {
    return;
  }
  }
  assert(0);
}

static void traverseVar(S_table env, int depth, A_var v)
{
  switch (v->kind)
  {
  case A_simpleVar:
  {
    E_escapeEntry x = S_look(env, v->u.simple);
    if (x && x->depth < depth)
    {
      x->escape = TRUE;
    }
    return;
  }
  case A_fieldVar:
  {
    return traverseVar(env, depth, v->u.field.var);
  }
  case A_subscriptVar:
  {
    traverseVar(env, depth, v->u.subscript.var);
    traverseExp(env, depth, v->u.subscript.exp);
    return;
  }
  }
  assert(0);
}

void Esc_findEscape(A_exp exp)
{
  S_table table = S_empty();
  traverseExp(table, depth, exp);
}
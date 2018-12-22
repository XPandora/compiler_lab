#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

#define MAXLINE 50

//Lab 6: put your code here
static void emit(AS_instr inst);
static void munchStm(T_stm s);
static Temp_temp munchExp(T_exp e);

static AS_instrList iList = NULL, last = NULL;
static AS_instrList prepare_args = NULL;

static void emit(AS_instr inst)
{
  if (last != NULL)
  {
    last->tail = AS_InstrList(inst, NULL);
    last = last->tail;
  }
  else
  {
    iList = last = AS_InstrList(inst, NULL);
  }
}

Temp_tempList L(Temp_temp h, Temp_tempList t)
{
  return Temp_TempList(h, t);
}

/* 
  helper function
*/

// imm->mem(r)
AS_instr imm_to_mem(int imm, Temp_temp r)
{
  char inst[MAXLINE];
  sprintf(inst, "movq $%d, (`s0)", imm);
  return AS_Oper(String(inst), NULL, L(r, NULL), NULL);
}

// reg->mem(r)
AS_instr reg_to_mem(Temp_temp src, Temp_temp r)
{
  char inst[MAXLINE];
  sprintf(inst, "movq `s0, (`s1)");
  return AS_Oper(String(inst), NULL, L(src, L(r, NULL)), NULL);
}

// imm->reg
AS_instr imm_to_reg(int imm, Temp_temp dst)
{
  char inst[MAXLINE];
  sprintf(inst, "movq $%d, `d0", imm);
  return AS_Oper(String(inst), L(dst, NULL), NULL, NULL);
}

// mem(r)->reg
AS_instr mem_to_reg(Temp_temp r, Temp_temp dst)
{
  char inst[MAXLINE];
  sprintf(inst, "movq (`s0), `d0");
  return AS_Oper(String(inst), L(dst, NULL), L(r, NULL), NULL);
}

// reg->reg
AS_instr reg_to_reg(Temp_temp src, Temp_temp dst)
{
  char inst[MAXLINE];
  sprintf(inst, "movq `s0, `d0");
  return AS_Move(String(inst), L(dst, NULL), L(src, NULL));
}

// str->reg
AS_instr str_to_reg(string str, Temp_temp dst)
{
  char inst[MAXLINE];
  sprintf(inst, "leaq %s, `d0", str);
  return AS_Oper(String(inst), L(dst, NULL), NULL, NULL);
}

// op with imm
AS_instr op_with_imm(string op, Temp_temp dst, int imm)
{
  char inst[MAXLINE];
  sprintf(inst, "%s $%d, `d0", op, imm);
  return AS_Oper(String(inst), L(dst, NULL), L(dst, NULL), NULL);
}

// op with reg
AS_instr op_with_reg(string op, Temp_temp src, Temp_temp dst)
{
  char inst[MAXLINE];
  sprintf(inst, "%s `s0, `d0", op);
  return AS_Oper(String(inst), L(dst, NULL), L(src, L(dst, NULL)), NULL);
}

// do with op
Temp_temp do_op(string op, T_exp left_exp, T_exp right_exp)
{
  Temp_temp result_temp = Temp_newtemp();
  if (left_exp->kind != T_CONST && right_exp->kind != T_CONST)
  {
    Temp_temp left_temp = munchExp(left_exp);
    Temp_temp right_temp = munchExp(right_exp);

    AS_instr inst1 = reg_to_reg(left_temp, result_temp);
    AS_instr inst2 = op_with_reg(op, right_temp, result_temp);
    emit(inst1);
    emit(inst2);
    return result_temp;
  }

  Temp_temp another_temp;
  int imm;
  if (left_exp->kind == T_CONST)
  {
    another_temp = munchExp(right_exp);
    imm = left_exp->u.CONST;
  }
  else
  {
    another_temp = munchExp(left_exp);
    imm = right_exp->u.CONST;
  }

  AS_instr inst1 = reg_to_reg(another_temp, result_temp);
  AS_instr inst2 = op_with_imm(op, result_temp, imm);
  emit(inst1);
  emit(inst2);

  return result_temp;
}

// reverse pushq sequence
void push_args(AS_instrList instrs)
{
  if (instrs == NULL)
  {
    return;
  }

  push_args(instrs->tail);
  emit(instrs->head);
}

static Temp_tempList munchArgs(int index, T_expList args)
{
  if (args == NULL)
  {
    return NULL;
  }

  AS_instr inst;
  bool isConst = (args->head->kind == T_CONST);
  Temp_temp dst_temp;
  switch (index)
  {
  case 1:
  {
    dst_temp = F_RDI();
    break;
  }
  case 2:
  {
    dst_temp = F_RSI();
    break;
  }
  case 3:
  {
    dst_temp = F_RDX();
    break;
  }
  case 4:
  {
    dst_temp = F_RCX();
    break;
  }
  case 5:
  {
    dst_temp = F_R8D();
    break;
  }
  case 6:
  {
    dst_temp = F_R9D();
    break;
  }
  default:
  {
    dst_temp = munchExp(args->head);
    inst = AS_Oper("pushq `s0", L(F_RSP(), NULL), L(dst_temp, L(F_RSP(), NULL)), NULL);
    prepare_args = AS_InstrList(inst, prepare_args);
    return munchArgs(index + 1, args->tail);
  }
  }

  Temp_temp src_temp = munchExp(args->head);
  inst = reg_to_reg(src_temp, dst_temp);
  prepare_args = AS_InstrList(inst, prepare_args);

  return Temp_TempList(dst_temp, munchArgs(index + 1, args->tail));
}

static void munchStm(T_stm s)
{
  switch (s->kind)
  {
  case T_SEQ:
  {
    printf("munchStm: T_SEQ should be eliminated");
    assert(0);
  }
  /*
    LABEL: 
  */
  case T_LABEL:
  {
    AS_instr inst = AS_Label(Temp_labelstring(s->u.LABEL), s->u.LABEL);
    emit(inst);
    return;
  }
  /*
    jmp label
  */
  case T_JUMP:
  {

    AS_instr inst = AS_Oper("jmp `j0", NULL, NULL, AS_Targets(s->u.JUMP.jumps));
    emit(inst);
    return;
  }
  /*
    cmpq reg, reg
    j.. label
  */
  case T_CJUMP:
  {
    T_exp left_exp = s->u.CJUMP.left;
    T_exp right_exp = s->u.CJUMP.right;

    Temp_temp left_temp = munchExp(left_exp);
    Temp_temp right_temp = munchExp(right_exp);

    AS_instr inst1 = AS_Oper("cmpq `s0, `s1", NULL, L(right_temp, L(left_temp, NULL)), NULL);

    // conditional true
    AS_instr inst2;
    switch (s->u.CJUMP.op)
    {
    case T_eq:
      inst2 = AS_Oper(String("je `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_ne:
      inst2 = AS_Oper(String("jne `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_lt:
      inst2 = AS_Oper(String("jl `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_le:
      inst2 = AS_Oper(String("jle `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_gt:
      inst2 = AS_Oper(String("jg `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_ge:
      inst2 = AS_Oper(String("jge `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_ult:
      inst2 = AS_Oper(String("jb `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_ule:
      inst2 = AS_Oper(String("jbe `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_ugt:
      inst2 = AS_Oper(String("ja `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    case T_uge:
      inst2 = AS_Oper(String("jae `j0"),
                      NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL)));
      break;
    default:
      printf("munchStm: unknown T_relop kind %d", s->u.CJUMP.op);
      assert(0);
    }

    // conditional false
    AS_instr inst3 = AS_Oper(String("jmp `j0"),
                             NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.false, NULL)));
    emit(inst1);
    emit(inst2);
    emit(inst3);
    return;
  }
  /*
    movq reg, reg
    movq reg, mem
    movq mem, reg
    movq imm, mem
    movq imm, reg
    ...can be very complex
  */
  case T_MOVE:
  {
    T_exp dst_exp = s->u.MOVE.dst;
    T_exp src_exp = s->u.MOVE.src;

    // ? -> mem
    if (dst_exp->kind == T_MEM)
    {
      Temp_temp r = munchExp(dst_exp->u.MEM);
      //  imm -> mem(r)
      if (src_exp->kind == T_CONST)
      {
        AS_instr inst = imm_to_mem(src_exp->u.CONST, r);
        emit(inst);
        return;
      }
      // reg -> mem(r)
      else
      {
        Temp_temp src = munchExp(src_exp);
        AS_instr inst = reg_to_mem(src, r);
        emit(inst);
        return;
      }
    }
    // ? -> reg
    else
    {
      Temp_temp dst = munchExp(dst_exp);

      // imm -> reg
      if (src_exp->kind == T_CONST)
      {
        AS_instr inst = imm_to_reg(src_exp->u.CONST, dst);
        emit(inst);
        return;
      }
      // mem(r) -> reg
      else if (src_exp->kind == T_MEM)
      {
        Temp_temp r = munchExp(src_exp->u.MEM);
        AS_instr inst = mem_to_reg(r, dst);
        emit(inst);
        return;
      }
      // reg -> reg
      else
      {
        Temp_temp src = munchExp(src_exp);
        AS_instr inst = reg_to_reg(src, dst);
        emit(inst);
        return;
      }
    }
  }
  case T_EXP:
  {
    munchExp(s->u.EXP);
    return;
  }
  default:
  {
    printf("munchStm: unknown stm kind %d", s->kind);
    assert(0);
  }
  }
}

static Temp_temp munchExp(T_exp e)
{
  switch (e->kind)
  {
  case T_BINOP:
  {
    T_exp left_exp = e->u.BINOP.left;
    T_exp right_exp = e->u.BINOP.right;
    switch (e->u.BINOP.op)
    {
    case T_plus:
    {
      return do_op("addq", left_exp, right_exp);
    }
    case T_minus:
    {
      return do_op("subq", left_exp, right_exp);
    }
    case T_mul:
    {
      return do_op("imulq", left_exp, right_exp);
    }
    case T_div:
    {
      // special for div
      Temp_temp result_temp = Temp_newtemp();
      Temp_temp left_temp = munchExp(left_exp);
      Temp_temp right_temp = munchExp(right_exp);

      AS_instr inst1 = reg_to_reg(left_temp, F_RAX());
      AS_instr inst2 = AS_Oper("cqto", L(F_RDX(), NULL), NULL, NULL);
      AS_instr inst3 = AS_Oper("idivq `s0", L(F_RAX(), NULL), L(right_temp, L(F_RAX(), L(F_RDX(), NULL))), NULL);
      AS_instr inst4 = reg_to_reg(F_RAX(), result_temp);

      emit(inst1);
      emit(inst2);
      emit(inst3);
      emit(inst4);
      return result_temp;
    }
    case T_and:
    {
      return do_op("andq", left_exp, right_exp);
    }
    case T_or:
    {
      return do_op("orq", left_exp, right_exp);
    }
    case T_lshift:
    {
      return do_op("shlq", left_exp, right_exp);
    }
    case T_rshift:
    {
      return do_op("shrq", left_exp, right_exp);
    }
    case T_arshift:
    {
      return do_op("sarq", left_exp, right_exp);
    }
    case T_xor:
    {
      return do_op("xorq", left_exp, right_exp);
    }
    default:
    {
      printf("munchExp: unknown T_binop kind %d", e->u.BINOP.op);
      assert(0);
    }
    }
  }
  case T_MEM:
  {
    Temp_temp dst = Temp_newtemp();
    Temp_temp r = munchExp(e->u.MEM);

    AS_instr inst = mem_to_reg(r, dst);
    emit(inst);
    return dst;
  }
  case T_TEMP:
  {
    return e->u.TEMP;
  }
  case T_ESEQ:
  {
    printf("munchExp: T_ESEQ should be eliminated");
    assert(0);
  }
  case T_NAME:
  {
    Temp_temp dst = Temp_newtemp();
    AS_instr inst = str_to_reg(Temp_labelstring(e->u.NAME), dst);
    emit(inst);
    return dst;
  }
  case T_CONST:
  {
    Temp_temp dst = Temp_newtemp();
    AS_instr inst = imm_to_reg(e->u.CONST, dst);
    emit(inst);
    return dst;
  }
  case T_CALL:
  {
    // check fun type
    if (e->u.CALL.fun->kind != T_NAME)
    {
      printf("munchExp: T_CALL func kind shoule be T_Name, but get %d", e->u.CALL.fun->kind);
      assert(0);
    }
    // caller saved registerss
    // r11 and r12
    Temp_temp r11_temp = Temp_newtemp();
    Temp_temp r10_temp = Temp_newtemp();
    emit(reg_to_reg(F_R11(), r11_temp));
    emit(reg_to_reg(F_R10(), r10_temp));

    // prepare args
    prepare_args = NULL;
    Temp_temp dst = Temp_newtemp();
    Temp_tempList arg_temps = munchArgs(0, e->u.CALL.args);
    push_args(prepare_args);

    AS_instr inst1 = AS_Oper("call `j0", L(F_RAX(), L(F_R11(), L(F_R10(), NULL))),
                             L(F_RDI(), L(F_RSI(), L(F_RDX(), L(F_RCX(), L(F_R8D(), L(F_R9D(), NULL)))))),
                             AS_Targets(Temp_LabelList(e->u.CALL.fun->u.NAME, NULL)));
    AS_instr inst2 = reg_to_reg(F_RAX(), dst);

    emit(inst1);
    emit(reg_to_reg(r11_temp, F_R11()));
    emit(reg_to_reg(r10_temp, F_R10()));
    emit(inst2);
    return dst;
  }
  default:
  {
    printf("munchExp: unknown exp kind %d", e->kind);
    assert(0);
  }
  }
}

AS_instrList F_codegen(F_frame f, T_stmList stmList)
{
  // initial instrList
  iList = NULL;
  last = NULL;
  // init params
  // get inreg params
  // mem params should be placed in mem before call
  F_accessList formals = F_formals(f);

  int index = 0;
  while (formals != NULL)
  {
    F_access access = formals->head;
    Temp_temp src_temp;
    switch (index)
    {
    case 1:
      src_temp = F_RDI();
      break;
    case 2:
      src_temp = F_RSI();
      break;
    case 3:
      src_temp = F_RDX();
      break;
    case 4:
      src_temp = F_RCX();
      break;
    case 5:
      src_temp = F_R8D();
      break;
    case 6:
      src_temp = F_R9D();
      break;
    default:
      index++;
      formals = formals->tail;
      continue;
    }

    // move param reg to frame use reg
    if (access->kind == inReg)
    {
      emit(reg_to_reg(src_temp, access->u.reg));
    }
    else
    {
      T_stm s = T_Move(T_Mem(T_Binop(T_plus, T_Const(access->u.offset), T_Temp(F_FP()))), T_Temp(src_temp));
      munchStm(s);
    }
    index++;
    formals = formals->tail;
  }

  // callee saved register in x86-64
  Temp_temp r12_temp = Temp_newtemp();
  Temp_temp r13_temp = Temp_newtemp();
  Temp_temp r14_temp = Temp_newtemp();
  Temp_temp r15_temp = Temp_newtemp();
  Temp_temp rbx_temp = Temp_newtemp();
  emit(reg_to_reg(F_R12(), r12_temp));
  emit(reg_to_reg(F_R13(), r13_temp));
  emit(reg_to_reg(F_R14(), r14_temp));
  emit(reg_to_reg(F_R15(), r15_temp));
  emit(reg_to_reg(F_RBX(), rbx_temp));

  // generate function body
  while (stmList)
  {
    munchStm(stmList->head);
    stmList = stmList->tail;
  }

  // restore callee saved register
  emit(reg_to_reg(r12_temp, F_R12()));
  emit(reg_to_reg(r13_temp, F_R13()));
  emit(reg_to_reg(r14_temp, F_R14()));
  emit(reg_to_reg(r15_temp, F_R15()));
  emit(reg_to_reg(rbx_temp, F_RBX()));

  emit(reg_to_reg(F_RBP(), F_RSP()));
  emit(AS_Oper("popq %rbp", L(F_RSP(), NULL), L(F_RSP(), L(F_RBP(), NULL)), NULL));
  emit(AS_Oper("ret", NULL, L(F_SP(), L(F_R12(), L(F_R13(), L(F_R14(), L(F_R15(), L(F_RBX(), NULL)))))), NULL));
  return iList;
}

#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"
#include <string.h>

/* 
	Register Alloc

	main phase:
		1.build
		2.simplify
		3.coalesce
		4.freeze
		5.potential spill
		6.select
		7.actual spill
*/

static bool inTempList(Temp_temp t, Temp_tempList l)
{
	if (l == NULL)
	{
		return FALSE;
	}

	if (l->head == t)
	{
		return TRUE;
	}

	return inTempList(t, l->tail);
}

static Temp_tempList replaceTempList(Temp_temp old, Temp_temp new, Temp_tempList tl)
{
	if (tl == NULL)
	{
		return tl;
	}

	if (tl->head == old)
	{
		return Temp_TempList(new, replaceTempList(old, new, tl->tail));
	}
	else
	{
		return Temp_TempList(tl->head, replaceTempList(old, new, tl->tail));
	}
}

static AS_instrList RewriteProgram(F_frame f, AS_instrList il, Temp_tempList spills)
{
	AS_instrList new_il = il;
	while (spills)
	{
		Temp_temp spill_temp = spills->head;
		spills = spills->tail;
		f->length += 8; // F_wordSize

		AS_instrList rewrite_il = new_il;
		while (rewrite_il)
		{
			AS_instr inst = rewrite_il->head;
			Temp_tempList src_templist = NULL;
			Temp_tempList dst_templist = NULL;

			if (inst->kind == I_MOVE)
			{
				src_templist = inst->u.MOVE.src;
				dst_templist = inst->u.MOVE.dst;
			}
			else if (inst->kind == I_OPER)
			{
				src_templist = inst->u.OPER.src;
				dst_templist = inst->u.OPER.dst;
			}

			// for definition, add store after
			if (inTempList(spill_temp, dst_templist))
			{
				Temp_temp t = Temp_newtemp();
				Temp_tempList new_tl = replaceTempList(spill_temp, t, dst_templist);

				if (inst->kind == I_MOVE)
				{
					inst->u.MOVE.dst = new_tl;
				}
				else if (inst->kind == I_OPER)
				{
					inst->u.OPER.dst = new_tl;
				}

				// new store
				char inst_c[100];
				sprintf(inst_c, "movq `s0, %d(`s1)", -f->length);
				AS_instr store_inst = AS_Oper(String(inst_c), NULL, Temp_TempList(t, Temp_TempList(F_RBP(), NULL)), NULL);

				rewrite_il->tail = AS_InstrList(store_inst, rewrite_il->tail);
			}
			else if (inTempList(spill_temp, src_templist))
			{
				Temp_temp t = Temp_newtemp();
				Temp_tempList new_tl = replaceTempList(spill_temp, t, src_templist);

				if (inst->kind == I_MOVE)
				{
					inst->u.OPER.src = new_tl;
				}
				else if (inst->kind == I_OPER)
				{
					inst->u.OPER.src = new_tl;
				}

				// new fetch
				char inst_c[100];
				sprintf(inst_c, "movq %d(`s0), `d0", -f->length);
				AS_instr fetch_inst = AS_Oper(String(inst_c), Temp_TempList(t, NULL), Temp_TempList(F_RBP(), NULL), NULL);

				rewrite_il->head = fetch_inst;
				rewrite_il->tail = AS_InstrList(inst, rewrite_il->tail);
				rewrite_il = rewrite_il->tail; // avoid dead loop
			}
			rewrite_il = rewrite_il->tail;
		}
	}

	return new_il;
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il)
{
	// generate flowgraph and live analysis

	G_graph flowgraph = FG_AssemFlowGraph(il, f);
	G_nodeList insts = G_nodes(flowgraph);

	struct Live_graph live_graph = Live_liveness(flowgraph);

	G_nodeList nodes = G_nodes(live_graph.graph);

	// start main phase
	struct COL_result col_result = COL_color(live_graph.graph, F_tempMap, NULL, live_graph.moves);

	if (col_result.spills != NULL)
	{
		// need rewrite
		AS_instrList new_il = RewriteProgram(f, il, col_result.spills);
		return RA_regAlloc(f, new_il);
	}
	struct RA_result ret;

	Temp_map color_map = Temp_layerMap(F_tempMap, Temp_layerMap(col_result.coloring, Temp_name()));
	AS_instrList *il_ptr = &il;
	while (*il_ptr)
	{
		AS_instr instr = (*il_ptr)->head;
		if (instr->kind == I_MOVE)
		{
			char *src = Temp_look(color_map, instr->u.MOVE.src->head);
			char *dst = Temp_look(color_map, instr->u.MOVE.dst->head);

			if (strncmp(src, dst, 4) == 0)
			{
				*il_ptr = (*il_ptr)->tail;
				continue;
			}
		}

		il_ptr = &((*il_ptr)->tail);
	}

	il_ptr = &il;
	while (*il_ptr)
	{
		AS_instr instr = (*il_ptr)->head;
		if (instr->kind == I_OPER && strncmp(instr->u.OPER.assem, "jmp", 3) == 0)
		{
			AS_instr next = (*il_ptr)->tail->head;
			if (next->kind == I_LABEL && next->u.LABEL.label == instr->u.OPER.jumps->labels->head)
			{
				*il_ptr = (*il_ptr)->tail;
				continue;
			}
		}

		il_ptr = &((*il_ptr)->tail);
	}

	ret.coloring = col_result.coloring;
	ret.il = AS_rewrite(il, f->length);
	return ret;
}

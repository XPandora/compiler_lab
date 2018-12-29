#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"

void showTempList(Temp_tempList list)
{
	Temp_map some_map = Temp_layerMap(F_tempMap, Temp_name());
	for (; list; list = list->tail)
	{
		printf("%s, ", Temp_look(some_map, list->head));
	}
	printf("\n");
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail)
{
	Live_moveList lm = (Live_moveList)checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}

static bool isSpecialTemp(Temp_temp t)
{
	return t == F_SP() || t == F_FP();
}

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

static bool inNodeList(G_node n, G_nodeList l)
{
	if (l == NULL)
	{
		return FALSE;
	}

	if (l->head == n)
	{
		return TRUE;
	}

	return inNodeList(n, l->tail);
}

static Temp_tempList union_tempList(Temp_tempList L, Temp_tempList R)
{
	while (R)
	{
		if (!inTempList(R->head, L))
		{
			L = Temp_TempList(R->head, L);
		}

		R = R->tail;
	}

	return L;
}

static Temp_tempList sub_tempList(Temp_tempList L, Temp_tempList R)
{
	Temp_tempList t = NULL;
	while (L)
	{
		if (!inTempList(L->head, R))
		{
			t = Temp_TempList(L->head, t);
		}
		L = L->tail;
	}

	return t;
}

static bool equal_tempList(Temp_tempList L, Temp_tempList R)
{
	Temp_tempList t;

	// L temp in R
	t = L;
	while (t)
	{
		if (!inTempList(t->head, R))
		{
			return FALSE;
		}
		t = t->tail;
	}

	// R temp in L
	t = R;
	while (t)
	{
		if (!inTempList(t->head, L))
		{
			return FALSE;
		}
		t = t->tail;
	}

	return TRUE;
}

void showInterference(G_graph interference, Live_moveList moves)
{
	printf("======== interference graph =====\n");
	G_nodeList nodes = G_nodes(interference);
	for (; nodes; nodes = nodes->tail)
	{
		G_node node = nodes->head;
		Temp_temp temp = G_nodeInfo(node);
		// if (Temp_look(F_tempMap, temp) != NULL)
		// { // precolored one are not interesting
		// 	continue;
		// }

		int count = 0;
		printf("%s:\n", Temp_look(Temp_layerMap(F_tempMap, Temp_name()), temp));
		printf(" conf: ");
		G_nodeList node_list;
		for (node_list = G_adj(node); node_list; node_list = node_list->tail)
		{
			printf("%s, ", Temp_look(Temp_layerMap(F_tempMap, Temp_name()), (Temp_temp)G_nodeInfo(node_list->head)));
			++count;
		}
		printf("(%d)\n move: ", count);
		count = 0;
		Live_moveList move_list;
		for (move_list = moves; move_list; move_list = move_list->tail)
		{
			if (move_list->src == node)
			{
				printf("(to)%s, ", Temp_look(Temp_layerMap(F_tempMap, Temp_name()), (Temp_temp)G_nodeInfo(move_list->dst)));
				++count;
			}
			else if (move_list->dst == node)
			{
				printf("(from)%s, ",
							 Temp_look(Temp_layerMap(F_tempMap, Temp_name()), (Temp_temp)G_nodeInfo(move_list->src)));
				++count;
			}
		}
		printf("(%d)\n", count);
	}
}

Temp_temp Live_gtemp(G_node n)
{
	//your code here.
	return G_nodeInfo(n);
}

struct Live_graph Live_liveness(G_graph flow)
{
	//your code here.
	struct Live_graph lg;
	G_nodeList nodes = G_nodes(flow);
	G_table in_table = G_empty();
	G_table out_table = G_empty();

	while (nodes)
	{
		G_enter(in_table, nodes->head, checked_malloc(sizeof(Temp_tempList)));
		G_enter(out_table, nodes->head, checked_malloc(sizeof(Temp_tempList)));
		nodes = nodes->tail;
	}

	bool finish = FALSE;

	printf("BEGIN Analysis\n");
	while (!finish)
	{
		//begin refresh in_table and out_table
		nodes = G_nodes(flow);
		finish = TRUE;
		// for each n
		while (nodes)
		{
			G_node cur_node = nodes->head;

			// in'[n] <- in[n], out'[n] <- out[n]
			Temp_tempList old_inTempList = *(Temp_tempList *)G_look(in_table, cur_node);
			Temp_tempList old_out_tempList = *(Temp_tempList *)G_look(out_table, cur_node);

			Temp_tempList new_inTempList = old_inTempList;
			Temp_tempList new_out_tempList = old_out_tempList;

			// in[n] <- use[n] ∪ (out[n] - def[n])
			new_inTempList = union_tempList(FG_use(cur_node),
																			sub_tempList(new_out_tempList, FG_def(cur_node)));

			// out[n] <- union all succ in[s], s is the succ of n
			G_nodeList succs = G_succ(cur_node);
			while (succs)
			{
				Temp_tempList succ_in_temp = *(Temp_tempList *)G_look(in_table, succs->head);
				new_out_tempList = union_tempList(new_out_tempList, succ_in_temp);
				succs = succs->tail;
			}

			if (!equal_tempList(old_inTempList, new_inTempList) ||
					!equal_tempList(old_out_tempList, new_out_tempList))
			{
				finish = FALSE;
			}

			*(Temp_tempList *)G_look(in_table, cur_node) = new_inTempList;
			*(Temp_tempList *)G_look(out_table, cur_node) = new_out_tempList;

			nodes = nodes->tail;
		}
	}
	printf("END Analysis\n");

	/* 
		construct interference_graph
	*/

	printf("BEGIN constrcut graph\n");
	G_graph interference_graph = G_Graph();
	TAB_table temp_to_node = TAB_empty();

	// precolored registers
	Temp_tempList hardRegs =
			Temp_TempList(F_RAX(),
										Temp_TempList(F_RBX(),
																	Temp_TempList(F_RCX(),
																								Temp_TempList(F_RDX(),
																															Temp_TempList(F_RSI(),
																																						Temp_TempList(F_RDI(),
																																													Temp_TempList(F_R8D(),
																																																				Temp_TempList(F_R9D(),
																																																											Temp_TempList(F_R10(),
																																																																		Temp_TempList(F_R11(),
																																																																									Temp_TempList(F_R12(),
																																																																																Temp_TempList(F_R13(),
																																																																																							Temp_TempList(F_R14(),
																																																																																														Temp_TempList(F_R15(), NULL))))))))))))));

	for (Temp_tempList temps = hardRegs; temps; temps = temps->tail)
	{
		G_node tempNode = G_Node(interference_graph, temps->head);
		TAB_enter(temp_to_node, temps->head, tempNode);
	}

	for (Temp_tempList temps = hardRegs; temps; temps = temps->tail)
	{
		for (Temp_tempList next = temps->tail; next; next = next->tail)
		{
			G_node a = TAB_look(temp_to_node, temps->head);
			G_node b = TAB_look(temp_to_node, next->head);
			G_addEdge(a, b);
		}
	}

	// enter nodes
	// attetion RSP and RBP should not enter in order to avoid coalese

	printf("BEGIN enter node\n");
	nodes = G_nodes(flow);
	while (nodes)
	{
		Temp_tempList use_tempList = FG_use(nodes->head);
		Temp_tempList def_tempList = FG_def(nodes->head);

		while (use_tempList)
		{
			Temp_temp temp = use_tempList->head;

			if (isSpecialTemp(temp))
			{
				use_tempList = use_tempList->tail;
				continue;
			}

			if (TAB_look(temp_to_node, temp) == NULL)
			{
				G_node temp_node = G_Node(interference_graph, temp);
				TAB_enter(temp_to_node, temp, temp_node);
			}

			use_tempList = use_tempList->tail;
		}

		while (def_tempList)
		{
			Temp_temp temp = def_tempList->head;

			if (isSpecialTemp(temp))
			{
				def_tempList = def_tempList->tail;
				continue;
			}

			if (TAB_look(temp_to_node, temp) == NULL)
			{
				G_node temp_node = G_Node(interference_graph, temp);
				TAB_enter(temp_to_node, temp, temp_node);
			}

			def_tempList = def_tempList->tail;
		}

		nodes = nodes->tail;
	}
	printf("BEGIN add edge\n");
	// add edge
	// attention to avoid add a edge twice

	nodes = G_nodes(flow);
	while (nodes)
	{
		Temp_tempList def_tempList = FG_def(nodes->head);
		Temp_tempList use_tempList = FG_def(nodes->head);

		while (def_tempList)
		{
			Temp_temp def_temp = def_tempList->head;
			Temp_tempList out_tempList = *(Temp_tempList *)G_look(out_table, nodes->head);
			G_node def_node = TAB_look(temp_to_node, def_temp);

			if (isSpecialTemp(def_temp))
			{
				def_tempList = def_tempList->tail;
				continue;
			}

			if (FG_isMove(nodes->head))
			{
				while (out_tempList)
				{
					Temp_temp out_temp = out_tempList->head;
					G_node out_node = TAB_look(temp_to_node, out_temp);

					if (isSpecialTemp(out_temp))
					{
						out_tempList = out_tempList->tail;
						continue;
					}

					// only add edge once
					if ((out_node != def_node) &&
							!inNodeList(out_node, G_adj(def_node)) &&
							!inTempList(out_temp, use_tempList))
					{
						G_addEdge(def_node, out_node);
					}
					out_tempList = out_tempList->tail;
				}
			}
			else
			{
				while (out_tempList)
				{
					Temp_temp out_temp = out_tempList->head;
					G_node out_node = TAB_look(temp_to_node, out_temp);

					if (isSpecialTemp(out_temp))
					{
						out_tempList = out_tempList->tail;
						continue;
					}

					// only add edge once
					if ((out_node != def_node) &&
							!inNodeList(out_node, G_adj(def_node)))
					{
						G_addEdge(def_node, out_node);
					}
					out_tempList = out_tempList->tail;
				}
			}

			def_tempList = def_tempList->tail;
		}

		nodes = nodes->tail;
	}
	printf("BEGIN constrcut move list\n");
	// construct move list
	Live_moveList moveList = NULL;
	nodes = G_nodes(flow);
	while (nodes)
	{
		if (FG_isMove(nodes->head))
		{
			AS_instr instr = G_nodeInfo(nodes->head);

			if (!isSpecialTemp(instr->u.MOVE.src->head) &&
					!isSpecialTemp(instr->u.MOVE.dst->head))
			{
				G_node src = TAB_look(temp_to_node, instr->u.MOVE.src->head);
				if (src == NULL)
				{
					printf("Live_liveness: src node can not be null\n");
					assert(0);
				}

				G_node dst = TAB_look(temp_to_node, instr->u.MOVE.dst->head);
				if (dst == NULL)
				{
					printf("Live_liveness: dst node can not be null\n");
					assert(0);
				}
				if (src != dst)
				{
					moveList = Live_MoveList(src, dst, moveList);
				}
			}
		}
		nodes = nodes->tail;
	}

	// showInterference(interference_graph, moveList);
	lg.graph = interference_graph;
	lg.moves = moveList;
	return lg;
}

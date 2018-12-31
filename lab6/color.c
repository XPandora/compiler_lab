#include <stdio.h>
#include <string.h>

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
#include "table.h"

#define K 14

// data structure for nodes
// every node belongs to only one of them
static G_nodeList precolored; // machine register set
static G_nodeList initial;		// temp regiter set

static G_nodeList simplifyWorklist; // low degree nodelist unrelated to move
static G_nodeList freezeWorklist;		// low degree nodelist related to move
static G_nodeList spillWorklist;		// high degree nodelist

static G_nodeList spilledNodes;		// set including nodes to be spilled in this loop
static G_nodeList coalescedNodes; // alreadt coalesced nodes set, when u <- v, v should added to this set
static G_nodeList coloredNodes;		// successfully colored nodes set
static G_nodeList selectStack;		// stack containing nodes deleted from graph

// data structure for move
// every move inst belongs to only one of them
static Live_moveList coalescedMoves;	 // already coalesced move-insts set
static Live_moveList constrainedMoves; // src-dst conflict move-insts set
static Live_moveList frozenMoves;			 // move insts that can not be coalesced
static Live_moveList worklistMoves;		 // move insts that can be coalessced(possible)
static Live_moveList activeMoves;			 // move insts unready for coalescing

// other structure
static G_table adjSet;	 // interference edges set, maybe unnecesary
static G_table adjList;	// interference nodes set
static G_table degree;	 // record degree information for every node
static G_table moveList; // record related move information for every node
static G_table alias;		 // when (u,v) coalesced, v in coalescedNodes, alias(v) = u
static G_table color;		 // color for every node

static string hard_regs[17] = {"none", "%rax", "%r10", "%r11", "%rbx", "%r12", "%r13", "%r14", "%r15",
															 "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9", "%rbp", "%rsp"};

/*
 * debug helper
 */
void showNodeList(G_nodeList list)
{
	Temp_map some_map = Temp_layerMap(F_tempMap, Temp_name());
	for (; list; list = list->tail)
	{
		printf("%s, ", Temp_look(some_map, (Temp_temp)G_nodeInfo(list->head)));
	}
	printf("\n");
}

void showMoveList(Live_moveList list)
{
	Temp_map some_map = Temp_layerMap(F_tempMap, Temp_name());
	for (; list; list = list->tail)
	{
		printf("%s->%s, ",
					 Temp_look(some_map, (Temp_temp)G_nodeInfo(list->src)),
					 Temp_look(some_map, (Temp_temp)G_nodeInfo(list->dst)));
	}
	printf("\n");
}

bool inMoveList(Live_moveList L, Live_moveList R)
{
	while (R)
	{
		if ((L->src == R->src && L->dst == R->dst) ||
				(L->dst == R->src && L->src == R->dst))
		{
			return TRUE;
		}
		R = R->tail;
	}

	return FALSE;
}

bool inNodeList(G_node n, G_nodeList l)
{
	while (l)
	{
		if (n == l->head)
		{
			return TRUE;
		}
		l = l->tail;
	}
	return FALSE;
}

G_nodeList union_nodelist(G_nodeList L, G_nodeList R)
{
	while (R)
	{
		if (!inNodeList(R->head, L))
		{
			L = G_NodeList(R->head, L);
		}
		R = R->tail;
	}

	return L;
}

G_nodeList sub_nodelist(G_nodeList L, G_nodeList R)
{
	G_nodeList nl = NULL;
	while (L)
	{
		if (!inNodeList(L->head, R))
		{
			nl = G_NodeList(L->head, nl);
		}
		L = L->tail;
	}
	return nl;
}

Live_moveList intersection_movelist(Live_moveList L, Live_moveList R)
{
	Live_moveList M = NULL;
	while (L)
	{
		if (inMoveList(L, R))
		{
			M = Live_MoveList(L->src, L->dst, M);
		}
		L = L->tail;
	}
	return M;
}
Live_moveList union_movelist(Live_moveList L, Live_moveList R)
{
	while (R)
	{
		if (!inMoveList(R, L))
		{
			L = Live_MoveList(R->src, R->dst, L);
		}
		R = R->tail;
	}
	return L;
}

Live_moveList sub_movelist(Live_moveList L, Live_moveList R)
{
	Live_moveList M = NULL;
	while (L)
	{
		if (!inMoveList(L, R))
		{
			M = Live_MoveList(L->src, L->dst, M);
		}
		L = L->tail;
	}
	return M;
}

/*
	ColorList
*/

typedef struct colorList_ *colorList;

struct colorList_
{
	int head;
	colorList tail;
};

colorList ColorList(int c, colorList tail)
{
	colorList cl = checked_malloc(sizeof(*cl));
	cl->head = c;
	cl->tail = tail;
	return cl;
}

colorList initColorList()
{
	colorList cl = NULL;
	for (int k = K; k > 0; k--)
	{
		cl = ColorList(k, cl);
	}
	return cl;
}

// modify?
colorList delete_colorlist(int c, colorList cl)
{
	colorList result = cl;

	colorList *p;
	for (p = &result; *p; p = &((*p)->tail))
	{
		if ((*p)->head == c)
		{
			*p = (*p)->tail;
			break;
		}
	}

	return result;
}

G_nodeList Adjacent(G_node n)
{
	G_nodeList initial_adjacents = G_look(adjList, n);
	return sub_nodelist(initial_adjacents, union_nodelist(selectStack, coalescedNodes));
}

Live_moveList NodeMoves(G_node n)
{
	Live_moveList ml = G_look(moveList, n);
	return intersection_movelist(ml, union_movelist(activeMoves, worklistMoves));
}

bool MoveRelated(G_node n)
{
	return NodeMoves(n) != NULL;
}

void EnableMoves(G_nodeList nodes)
{
	while (nodes)
	{
		G_node n = nodes->head;
		Live_moveList ml = NodeMoves(n);
		while (ml)
		{
			Live_moveList m = Live_MoveList(ml->src, ml->dst, NULL);
			if (inMoveList(m, activeMoves))
			{
				assert(activeMoves != NULL);
				activeMoves = sub_movelist(activeMoves, m);
				worklistMoves = union_movelist(worklistMoves, m);
			}
			ml = ml->tail;
		}

		nodes = nodes->tail;
	}
}

void DecrementDegree(G_node n)
{
	int *degree_num = G_look(degree, n);
	assert(degree_num != NULL);
	int d = *degree_num;
	(*degree_num)--;

	if (d == K)
	{
		EnableMoves(union_nodelist(G_NodeList(n, NULL), Adjacent(n)));
		spillWorklist = sub_nodelist(spillWorklist, G_NodeList(n, NULL));

		if (!inNodeList(n, precolored))
		{
			if (MoveRelated(n))
			{
				freezeWorklist = union_nodelist(freezeWorklist, G_NodeList(n, NULL));
			}
			else
			{
				simplifyWorklist = union_nodelist(simplifyWorklist, G_NodeList(n, NULL));
			}
		}
	}
}

static void Build(G_graph ig, Temp_map precolored_map, Live_moveList moves)
{
	// initial
	precolored = NULL;
	initial = NULL;
	simplifyWorklist = NULL;
	freezeWorklist = NULL;
	spillWorklist = NULL;

	spilledNodes = NULL;
	coalescedNodes = NULL;
	coloredNodes = NULL;
	selectStack = NULL;

	coalescedMoves = NULL;
	constrainedMoves = NULL;
	frozenMoves = NULL;
	worklistMoves = NULL;
	activeMoves = NULL;

	adjSet = G_empty();
	adjList = G_empty();
	degree = G_empty();
	moveList = G_empty();
	alias = G_empty();
	color = G_empty();

	// precolored, initials and color
	G_nodeList nodes = G_nodes(ig);
	while (nodes)
	{
		G_node node = nodes->head;
		Temp_temp temp = Live_gtemp(node);
		if (Temp_look(precolored_map, temp) != NULL)
		{
			precolored = G_NodeList(node, precolored);
			int *color_num = checked_malloc(sizeof(int));
			if (temp == F_RAX())
			{
				*color_num = 1;
			}
			else if (temp == F_R10())
			{
				*color_num = 2;
			}
			else if (temp == F_R11())
			{
				*color_num = 3;
			}
			else if (temp == F_RBX())
			{
				*color_num = 4;
			}
			else if (temp == F_R12())
			{
				*color_num = 5;
			}
			else if (temp == F_R13())
			{
				*color_num = 6;
			}
			else if (temp == F_R14())
			{
				*color_num = 7;
			}
			else if (temp == F_R15())
			{
				*color_num = 8;
			}
			else if (temp == F_RDI())
			{
				*color_num = 9;
			}
			else if (temp == F_RSI())
			{
				*color_num = 10;
			}
			else if (temp == F_RDX())
			{
				*color_num = 11;
			}
			else if (temp == F_RCX())
			{
				*color_num = 12;
			}
			else if (temp == F_R8D())
			{
				*color_num = 13;
			}
			else if (temp == F_R9D())
			{
				*color_num = 14;
			}
			else if (temp == F_RBP())
			{
				*color_num = 15;
			}
			else if (temp == F_RSP())
			{
				*color_num = 16;
			}
			else
			{
				printf("Build: unknown precolored register\n");
				assert(0);
			}
			G_enter(color, node, color_num);
		}
		else
		{
			initial = G_NodeList(node, initial);
		}

		nodes = nodes->tail;
	}

	// adjList, degree
	nodes = G_nodes(ig);
	while (nodes)
	{
		G_node node = nodes->head;
		G_nodeList adj_nodes = G_adj(node);
		G_enter(adjList, node, adj_nodes);
		if (Live_gtemp(node) == F_RAX())
		{
			printf("rax adj:");
			showNodeList(adj_nodes);
		}

		int *degree_num = checked_malloc(sizeof(int));
		*degree_num = 0;
		while (adj_nodes)
		{
			(*degree_num)++;
			adj_nodes = adj_nodes->tail;
		}
		G_enter(degree, node, degree_num);
		nodes = nodes->tail;
	}

	// moveList, worklistMoves
	Live_moveList temp_moves = moves;

	while (temp_moves)
	{
		if (temp_moves->src != temp_moves->dst &&
				!inMoveList(temp_moves, worklistMoves))
		{
			worklistMoves = Live_MoveList(temp_moves->src, temp_moves->dst, worklistMoves);
		}

		temp_moves = temp_moves->tail;
	}

	temp_moves = worklistMoves;
	while (temp_moves)
	{
		G_node src = temp_moves->src;
		G_node dst = temp_moves->dst;

		Live_moveList src_old = G_look(moveList, src);
		Live_moveList dst_old = G_look(moveList, dst);

		G_enter(moveList, src, Live_MoveList(src, dst, src_old));
		G_enter(moveList, dst, Live_MoveList(src, dst, dst_old));

		temp_moves = temp_moves->tail;
	}
}

static void MakeWorklist()
{
	while (initial)
	{
		int *degree_num = G_look(degree, initial->head);
		assert(degree_num != NULL);
		if ((*degree_num) >= K)
		{
			spillWorklist = G_NodeList(initial->head, spillWorklist);
		}
		else if (MoveRelated(initial->head))
		{
			freezeWorklist = G_NodeList(initial->head, freezeWorklist);
		}
		else
		{
			simplifyWorklist = G_NodeList(initial->head, simplifyWorklist);
		}
		initial = initial->tail;
	}
}

static void Simplify()
{
	G_node n = simplifyWorklist->head;
	simplifyWorklist = simplifyWorklist->tail;

	selectStack = G_NodeList(n, selectStack);
	G_nodeList adjacent_nodes = Adjacent(n);

	while (adjacent_nodes)
	{
		DecrementDegree(adjacent_nodes->head);
		adjacent_nodes = adjacent_nodes->tail;
	}
}

void AddEdge(G_node u, G_node v)
{
	G_nodeList u_adjacents = G_look(adjList, u);
	G_nodeList v_adjacents = G_look(adjList, v);
	if (!inNodeList(v, u_adjacents) && u != v)
	{
		u_adjacents = G_NodeList(v, u_adjacents);
		G_enter(adjList, u, u_adjacents);
		int *degree_num = G_look(degree, u);
		if (degree_num == NULL)
		{
			printf("AddEdge: u degree null\n");
			assert(0);
		}
		(*degree_num)++;

		v_adjacents = G_NodeList(u, v_adjacents);
		G_enter(adjList, v, v_adjacents);
		degree_num = G_look(degree, v);
		if (degree_num == NULL)
		{
			printf("AddEdge: v degree null\n");
			assert(0);
		}
		(*degree_num)++;
	}
}

void AddWorkList(G_node u)
{
	int *degree_num = G_look(degree, u);
	assert(degree_num != NULL);
	if (!inNodeList(u, precolored) &&
			!MoveRelated(u) &&
			(*degree_num) < K)
	{
		freezeWorklist = sub_nodelist(freezeWorklist, G_NodeList(u, NULL));
		simplifyWorklist = union_nodelist(simplifyWorklist, G_NodeList(u, NULL));
	}
}

bool OK(G_node t, G_node r)
{
	int *degree_num = G_look(degree, t);
	bool flag1 = (*degree_num) < K;
	bool flag2 = inNodeList(t, precolored);
	G_nodeList adjacent_nodes = G_look(adjList, t);
	bool flag3 = inNodeList(r, adjacent_nodes);

	return flag1 || flag2 || flag3;
}

bool AdjacentOK(G_node v, G_node u)
{
	G_nodeList v_adjacents = Adjacent(v);
	while (v_adjacents)
	{
		G_node t = v_adjacents->head;
		if (!OK(t, u))
		{
			return FALSE;
		}
		v_adjacents = v_adjacents->tail;
	}

	return TRUE;
}

bool Conservative(G_nodeList nodes)
{
	int k = 0;
	while (nodes)
	{
		G_node n = nodes->head;
		int *degree_num = G_look(degree, n);
		if ((*degree_num) >= K)
		{
			k++;
		}

		nodes = nodes->tail;
	}

	return k < K;
}

G_node GetAlias(G_node n)
{
	if (inNodeList(n, coalescedNodes))
	{
		G_node m = G_look(alias, n);
		assert(m != NULL);
		return GetAlias(m);
	}
	else
	{
		return n;
	}
}

void Combine(G_node u, G_node v)
{
	if (inNodeList(v, freezeWorklist))
	{
		freezeWorklist = sub_nodelist(freezeWorklist, G_NodeList(v, NULL));
	}
	else
	{
		spillWorklist = sub_nodelist(spillWorklist, G_NodeList(v, NULL));
	}
	coalescedNodes = union_nodelist(coalescedNodes, G_NodeList(v, NULL));
	G_enter(alias, v, u);
	Live_moveList u_ml = G_look(moveList, u);
	Live_moveList v_ml = G_look(moveList, v);

	G_enter(moveList, u, union_movelist(u_ml, v_ml));
	EnableMoves(G_NodeList(v, NULL));

	G_nodeList v_adjacents = Adjacent(v);
	while (v_adjacents)
	{
		G_node t = v_adjacents->head;
		AddEdge(t, u);
		DecrementDegree(t);

		v_adjacents = v_adjacents->tail;
	}

	int *degree_num = G_look(degree, u);
	// attention
	if ((*degree_num) >= K && inNodeList(u, freezeWorklist) && !inNodeList(u, precolored))
	{
		freezeWorklist = sub_nodelist(freezeWorklist, G_NodeList(u, NULL));
		spillWorklist = union_nodelist(spillWorklist, G_NodeList(u, NULL));
	}
}

static void Coalesce()
{
	Live_moveList m = Live_MoveList(worklistMoves->src, worklistMoves->dst, NULL);
	G_node x = GetAlias(worklistMoves->src);
	G_node y = GetAlias(worklistMoves->dst);

	G_node u, v;
	if (inNodeList(y, precolored))
	{
		u = y;
		v = x;
	}
	else
	{
		u = x;
		v = y;
	}

	worklistMoves = worklistMoves->tail;
	if (u == v)
	{
		coalescedMoves = union_movelist(coalescedMoves, m);
		AddWorkList(u);
	}
	else if (inNodeList(v, precolored) || inNodeList(v, (G_nodeList)G_look(adjList, u)))
	{
		constrainedMoves = union_movelist(constrainedMoves, m);
		AddWorkList(u);
		AddWorkList(v);
	}
	else if ((inNodeList(u, precolored) && AdjacentOK(v, u)) ||
					 (!inNodeList(u, precolored) && Conservative(union_nodelist(Adjacent(u), Adjacent(v)))))
	{
		coalescedMoves = union_movelist(coalescedMoves, m);
		Combine(u, v);
		AddWorkList(u);
	}
	else
	{
		activeMoves = union_movelist(activeMoves, m);
	}
}

void FreezeMoves(G_node u)
{
	Live_moveList ml = NodeMoves(u);
	while (ml)
	{
		Live_moveList m = Live_MoveList(ml->src, ml->dst, NULL);
		G_node x = m->src;
		G_node y = m->dst;

		G_node v;
		if (GetAlias(y) == GetAlias(u))
		{
			v = GetAlias(x);
		}
		else
		{
			v = GetAlias(y);
		}

		activeMoves = sub_movelist(activeMoves, m);
		frozenMoves = union_movelist(frozenMoves, m);

		int *degree_num = G_look(degree, v);
		if (NodeMoves(v) == NULL && (*degree_num) < K)
		{
			freezeWorklist = sub_nodelist(freezeWorklist, G_NodeList(v, NULL));
			simplifyWorklist = union_nodelist(simplifyWorklist, G_NodeList(v, NULL));
		}

		ml = ml->tail;
	}
}

static void Freeze()
{
	G_node u = freezeWorklist->head;
	freezeWorklist = freezeWorklist->tail;
	simplifyWorklist = union_nodelist(simplifyWorklist, G_NodeList(u, NULL));
	FreezeMoves(u);
}

static void SelectSpill()
{
	G_nodeList potentialSpills = spillWorklist;
	int max_degree = -1;
	G_node m = NULL;

	while (potentialSpills)
	{
		int *degree_num = G_look(degree, potentialSpills->head);
		if ((*degree_num) > max_degree)
		{
			m = potentialSpills->head;
			max_degree = *degree_num;
		}

		potentialSpills = potentialSpills->tail;
	}

	spillWorklist = sub_nodelist(spillWorklist, G_NodeList(m, NULL));
	simplifyWorklist = union_nodelist(simplifyWorklist, G_NodeList(m, NULL));
	FreezeMoves(m);
}

static void AssignColor()
{
	while (selectStack)
	{
		G_node n = selectStack->head;
		selectStack = selectStack->tail;

		colorList okColors = initColorList();
		G_nodeList n_adjacents = G_look(adjList, n);
		while (n_adjacents)
		{
			G_node w = n_adjacents->head;
			if (inNodeList(GetAlias(w), union_nodelist(coloredNodes, precolored)))
			{
				int *color_num = G_look(color, GetAlias(w));
				okColors = delete_colorlist(*color_num, okColors);
			}
			n_adjacents = n_adjacents->tail;
		}

		if (okColors == NULL)
		{
			spilledNodes = union_nodelist(spilledNodes, G_NodeList(n, NULL));
		}
		else
		{
			coloredNodes = union_nodelist(coloredNodes, G_NodeList(n, NULL));
			int *c = checked_malloc(sizeof(int));
			*c = okColors->head;
			G_enter(color, n, c);
		}
	}
	// printf("coloredNodes:");
	// showNodeList(coloredNodes);
	G_nodeList nodes = coalescedNodes;
	while (nodes)
	{
		G_node n = nodes->head;
		int *c = G_look(color, GetAlias(n));
		assert(c != NULL);
		G_enter(color, n, c);
		nodes = nodes->tail;
	}
}

struct COL_result COL_color(G_graph ig, Temp_map precolored_map, Temp_tempList regs, Live_moveList moves)
{
	/*
		build
	*/
	// graph has been given, just initial data structures
	// printf("Build\n");
	Build(ig, precolored_map, moves);

	/*
		MakeWorklist
	*/
	// printf("MakeWorklist\n");
	MakeWorklist();

	// begin repeat
	while (simplifyWorklist != NULL ||
				 worklistMoves != NULL ||
				 freezeWorklist != NULL ||
				 spillWorklist != NULL)
	{
		// printf("======== before this round of coloring =======\n");
		// printf("simplifyWorklist: ");
		// showNodeList(simplifyWorklist);
		// printf("worklistMoves: ");
		// showMoveList(worklistMoves);
		// printf("freezeWorklist: ");
		// showNodeList(freezeWorklist);
		// printf("spillWorklist: ");
		// showNodeList(spillWorklist);

		// printf("coalescedNodes: ");
		// showNodeList(coalescedNodes);
		// printf("selectStack: ");
		// showNodeList(selectStack);
		// printf("coalescedMoves: ");
		// showMoveList(coalescedMoves);
		// printf("constrainedMoves: ");
		// showMoveList(constrainedMoves);
		// printf("frozenMoves: ");
		// showMoveList(frozenMoves);
		// printf("activeMoves: ");
		// showMoveList(activeMoves);

		if (simplifyWorklist != NULL)
		{
			printf("Simplify\n");
			Simplify();
		}
		else if (worklistMoves != NULL)
		{
			printf("Coalesce\n");
			Coalesce();
		}
		else if (freezeWorklist != NULL)
		{
			printf("Freeze\n");
			Freeze();
		}
		else if (spillWorklist != NULL)
		{
			printf("SelectSpill\n");
			SelectSpill();
		}
	}

	// printf("AssignColor\n");
	AssignColor();
	struct COL_result ret;
	// constrcuct coloring
	// printf("Construct coloring\n");
	Temp_map coloring = Temp_empty();
	G_nodeList nodes = union_nodelist(coloredNodes, coalescedNodes);
	while (nodes)
	{
		G_node n = nodes->head;
		int *c = G_look(color, n);
		if (c == NULL)
		{
			printf("COL_color: G_look result is null\n");
			assert(0);
		}
		Temp_temp t = Live_gtemp(n);

		Temp_enter(coloring, t, String(hard_regs[*c]));
		nodes = nodes->tail;
	}

	// construct spills
	Temp_tempList spills = NULL;
	G_nodeList actuallSpills = spilledNodes;
	while (actuallSpills)
	{
		G_node spill_node = actuallSpills->head;
		Temp_temp t = Live_gtemp(spill_node);
		spills = Temp_TempList(t, spills);

		actuallSpills = actuallSpills->tail;
	}

	ret.coloring = coloring;
	ret.spills = spills;
	return ret;
}

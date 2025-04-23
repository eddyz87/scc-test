#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define U32_MAX		((u32)~0U)

typedef unsigned int u32;
typedef unsigned char bool;

enum {
	false = 0, true = 1
};

enum {
	GFP_KERNEL
};

enum {
	MAX_VERTEX_NUM = 32
};

static void *kvcalloc(size_t num, size_t sz, unsigned flags)
{
	return calloc(num, sz);
}

static void kvfree(void *mem)
{
	free(mem);
}

static u32 min(u32 a, u32 b)
{
	return a < b ? a : b;
}

struct bpf_prog {
	u32 len;
	u32 successors[MAX_VERTEX_NUM][2];
	bool visited[MAX_VERTEX_NUM];
	bool dfs_stack[MAX_VERTEX_NUM * 2];
	bool reachable[MAX_VERTEX_NUM][MAX_VERTEX_NUM];
};

struct bpf_insn_aux_data {
	u32 scc;
};

struct bpf_scc_info {};

struct bpf_verifier_env {
	struct bpf_insn_aux_data insn_aux_data[MAX_VERTEX_NUM];
	struct bpf_prog *prog;
	struct bpf_scc_info *scc_info;
	u32 num_sccs;
};

static int insn_successors(struct bpf_prog *prog, u32 idx, u32 succ[2])
{
	succ[0] = prog->successors[idx][0];
	succ[1] = prog->successors[idx][1];
	if (succ[0] == U32_MAX)
		return 0;
	if (succ[1] == U32_MAX)
		return 1;
	return 2;
}

static int compute_scc(struct bpf_verifier_env *env)
{
	const u32 NOT_ON_STACK = U32_MAX;

	struct bpf_insn_aux_data *aux = env->insn_aux_data;
	const u32 insn_cnt = env->prog->len;
	int stack_sz, dfs_sz, err = 0;
	u32 *stack, *pre, *low, *dfs;
	u32 succ_cnt, i, j, t, w;
	u32 next_preorder_num;
	u32 next_scc_id;
	bool assign_scc;
	u32 succ[2];

	next_preorder_num = 1;
	next_scc_id = 1;
	/* - 'stack' accumulates vertices in DFS order, see invariant comment below;
	 * - 'pre[t] == p' => preorder number of vertex 't' is 'p';
	 * - 'low[t] == n' => smallest preorder number of the vertex reachable from 't' is 'n';
	 * - 'dfs' DFS traversal stack, used to emulate explicit recursion.
	 */
	stack = kvcalloc(insn_cnt, sizeof(int), GFP_KERNEL);
	pre = kvcalloc(insn_cnt, sizeof(int), GFP_KERNEL);
	low = kvcalloc(insn_cnt, sizeof(int), GFP_KERNEL);
	dfs = kvcalloc(insn_cnt, sizeof(*dfs), GFP_KERNEL);
	if (!stack || !pre || !low || !dfs) {
		err = -ENOMEM;
		goto exit;
	}
	/*
	 * References:
	 * [1] R. Tarjan "Depth-First Search and Linear Graph Algorithms"
	 * [2] D. J. Pearce "A Space-Efficient Algorithm for Finding Strongly Connected Components"
	 *
	 * Algorithm maintains the following invariant:
	 * - suppose there is a path 'u' ~> 'v', such that 'pre[u] < pre[v]';
	 * - vertex 'u' remains on stack while vertex 'v' remains on stack.
	 *
	 * Consequently:
	 * - If 'low[v] < pre[v]' there is a path from 'v' to some vertex 'u',
	 *   such that 'pre[u] == low[v]', vertex 'u' is currently on the stack
	 *   and thus there is an SCC (loop) containing both 'u' and 'v'.
	 * - If 'low[v] == pre[v]' loops containing 'v' are already explored,
	 *   'v' can be considered a root of an SCC.
	 * - Because of the 'pre[u] < pre[v]' property u's index in 'dfs' is smaller
	 *   than v's index in 'dfs'.
	 *
	 * Here is a pseudo-code for an explicitly recursive version of the algorithm:
	 *
	 *    NOT_ON_STACK = insn_cnt + 1
	 *    pre = [0] * insn_cnt
	 *    low = [0] * insn_cnt
	 *    scc = [0] * insn_cnt
	 *    stack = []
	 *
	 *    next_preorder_num = 1
	 *    next_scc_id = 1
	 *
	 *    def recur(w):
	 *        nonlocal next_preorder_num
	 *        nonlocal next_scc_id
	 *
	 *        pre[w] = next_preorder_num
	 *        low[w] = next_preorder_num
	 *        next_preorder_num += 1
	 *        stack.append(w)
	 *        for s in successors(w):
	 *            # Note: for classic algorithm the block below should look as:
	 *            #
	 *            # if pre[s] == 0:
	 *            #     recur(s)
	 *            #	    low[w] = min(low[w], low[s])
	 *            # elif low[s] != NOT_ON_STACK:
	 *            #     low[w] = min(low[w], pre[s])
	 *            #
	 *            # But replacing both 'min' instructions with 'low[w] = min(low[w], low[s])'
	 *            # does not break the invariant and makes itartive version of the algorithm
	 *            # simpler. See 'Algorithm #3' from [2].
	 *
	 *            # 's' not yet visited
	 *            if pre[s] == 0:
	 *                recur(s)
	 *            # if 's' is on stack, pick lowest reachable preorder number from it;
	 *            # if 's' is not on stack 'low[s] == NOT_ON_STACK > low[w]' so 'min' would be a noop.
	 *            low[w] = min(low[w], low[s])
	 *
	 *        if low[w] == pre[w]:
	 *            # 'w' is the root of an SCC, pop all vertices
	 *            # below 'w' on stack and assign same SCC to them.
	 *            while True:
	 *                t = stack.pop()
	 *                low[t] = NOT_ON_STACK
	 *                scc[t] = next_scc_id
	 *                if t == w:
	 *                    break
	 *            next_scc_id += 1
	 *
	 *    for i in range(0, insn_cnt):
	 *        if pre[i] == 0:
	 *            recur(i)
	 *
	 * Below implementation replaces explicit recusion with array 'dfs'.
	 */
	for (i = 0; i < insn_cnt; i++) {
		if (pre[i])
			continue;
		stack_sz = 0;
		dfs_sz = 1;
		dfs[0] = i;
dfs_continue:
		while (dfs_sz) {
			w = dfs[dfs_sz - 1];
			if (pre[w] == 0) {
				low[w] = next_preorder_num;
				pre[w] = next_preorder_num;
				next_preorder_num++;
				stack[stack_sz++] = w;
			}
			/* Visit 'w' successors */
			succ_cnt = insn_successors(env->prog, w, succ);
			for (j = 0; j < succ_cnt; ++j) {
				if (pre[succ[j]]) {
					low[w] = min(low[w], low[succ[j]]);
				} else {
					dfs[dfs_sz++] = succ[j];
					goto dfs_continue;
				}
			}
			/* Preserve the invariant: if some not above in stack
			 * is reachable from 'w', keep 'w' on stack.
			 */
			if (low[w] < pre[w]) {
				dfs_sz--;
				goto dfs_continue;
			}
			/* Assign SCC number only if component has two or more elements,
			 * or if component has a self reference.
			 */
			assign_scc = stack[stack_sz - 1] != w;
			for (j = 0; j < succ_cnt; ++j) {
				if (succ[j] == w) {
					assign_scc = true;
					break;
				}
			}
			/* Pop component elements from stack */
			do {
				t = stack[--stack_sz];
				low[t] = NOT_ON_STACK;
				if (assign_scc)
					aux[t].scc = next_scc_id;
			} while (t != w);
			if (assign_scc)
				next_scc_id++;
			dfs_sz--;
		}
	}
	env->scc_info = kvcalloc(next_scc_id, sizeof(*env->scc_info), GFP_KERNEL);
	if (!env->scc_info) {
		err = -ENOMEM;
		goto exit;
	}
	env->num_sccs = next_scc_id;
exit:
	kvfree(stack);
	kvfree(pre);
	kvfree(low);
	kvfree(dfs);
	return err;
}

/* Compute which vertexes are reachable from a given vertex in a
 * simplest way possible: do a DFS while maintaining visited set.
 */
static void compute_reachable_aux(struct bpf_prog *p, int v)
{
	u32 succ_cnt, succ[2];
	int w, i, dfs_sz;

        memset(p->visited, 0, sizeof(p->visited));
	dfs_sz = 1;
	p->dfs_stack[0] = v;
	while (dfs_sz) {
		w = p->dfs_stack[--dfs_sz];
		if (p->visited[w])
			continue;
		p->visited[w] = true;
		succ_cnt = insn_successors(p, w, succ);
		for (i = 0; i < succ_cnt; ++i) {
			p->dfs_stack[dfs_sz++] = succ[i];
			p->reachable[v][succ[i]] = true;
		}
	}
}

static void compute_reachable(struct bpf_prog *p)
{
	for (int v = 0; v < p->len; ++v)
		compute_reachable_aux(p, v);
}

static void generate_graph(struct bpf_prog *p) {
	int v, r, s, succ_cnt;

        p->len = random() % MAX_VERTEX_NUM;
        for (v = 0; v < p->len; ++v) {
		r = random() % 10;
                if (r < 6)
			succ_cnt = 1;
                else if (r < 9)
			succ_cnt = 2;
                else
			succ_cnt = 0;
		p->successors[v][0] = U32_MAX;
		p->successors[v][1] = U32_MAX;
                for (s = 0; s < succ_cnt; ++s)
			p->successors[v][s] = random() % p->len;
        }
}

static void show_graph(struct bpf_verifier_env *env)
{
	struct bpf_prog *p = env->prog;
	int s, v, u;

	printf("digraph G {\n");
	for (v = 0; v < p->len; ++v) {
		if (env->insn_aux_data[v].scc)
			printf("  %d [label=\"%d: #%d\"];\n", v, v, env->insn_aux_data[v].scc);
		else
			printf("  %d [label=\"%d\"];\n", v, v);
		for (s = 0; s < 2; ++s) {
			if (p->successors[v][s] == U32_MAX)
				break;
			printf("  %d -> %d;\n", v, p->successors[v][s]);
		}
	}
	printf("}\n");

	for (v = 0; v < p->len; ++v) {
		printf("%d: ", v);
		for (u = 0; u < p->len; ++u) {
			if (p->reachable[v][u])
				printf(" %d", u);
		}
		printf("\n");
	}
}

static void exit_with_error(int seed, struct bpf_verifier_env *env, char *fmt, ...)
{
	va_list args;

	fprintf(stderr, "seed %d: ", seed);
	va_start(args, fmt);
	vfprintf(stderr, fmt, args);
	va_end(args);
	show_graph(env);
	exit(1);
}

static void check_sccs(int seed, struct bpf_verifier_env *env)
{
	struct bpf_prog *p = env->prog;
	int u, v;

	for (u = 0; u < p->len; ++u) {
		for (v = 0; v < p->len; ++v) {
			bool expect_same_scc = p->reachable[u][v] && p->reachable[v][u];
                        bool computed_same_scc =
                            env->insn_aux_data[v].scc != 0 &&
                            env->insn_aux_data[v].scc == env->insn_aux_data[u].scc;
                        if (expect_same_scc != computed_same_scc) {
				exit_with_error(seed, env,
						"scc mismatch between %d and %d (expected %d, computed %d)\n",
						u, v, expect_same_scc, computed_same_scc);
                        }
		}
	}
}

/* For a small graph G verify that SCCs computed by compute_scc are correct:
 * - generate a small graph
 * - use DFS to compute a matrix of vertexes reachable from each vertex
 * - compute SCCs using compute_scc
 * - for each pair of vertexes 'v' reachable from 'u':
 *   - if 'u' is also reachable from 'v' then 'u' and 'v' must be in a same SCC;
 *   - otherwise 'u' and 'v' must be in different SCCs.
 * - for each pair of vertexes 'v' not reachable from 'u', 'u' and 'v' must
 *   be in different SCCs.
 */
static void test_once(int seed)
{
	struct bpf_verifier_env env = {};
	struct bpf_prog p = {};
	int err;

	env.prog = &p;
        srandom(seed);
        generate_graph(&p);
        compute_reachable(&p);
	err = compute_scc(&env);
        kvfree(env.scc_info);
	if (err)
		exit_with_error(seed, &env, "compute_scc returned error: %d\n", err);
	check_sccs(seed, &env);
}

int main(int argc, char *argv[])
{
	int seed, i;

	if (argc == 2) {
		seed = atoi(argv[1]);
		test_once(seed);
	} else {
		srandom(clock());
		for (i = 0; i < 1000 * 1000; ++i) {
			seed = random();
			test_once(seed);
		}
		printf("All ok\n");
	}

}

#include <stdio.h>
#include <string.h>

#define MAX_NODES 1024
#define MAX_ADJ   128

#define EPSILON  -1
#define BOTTOM   -2

/* ---------- ID mapping ---------- */
static int id_keys[MAX_NODES];
static int id_vals[MAX_NODES];
static int id_size = 0;
static int nxt     = 0;

int get_id(int x) {
    for (int i = 0; i < id_size; i++)
        if (id_keys[i] == x) return id_vals[i];
    id_keys[id_size] = x;
    id_vals[id_size] = nxt;
    id_size++;
    return nxt++;
}

/* ---------- Graph ---------- */
static int adj[MAX_NODES][MAX_ADJ];
static int deg[MAX_NODES];

static int imax(int a, int b) { return a > b ? a : b; }

int main(void) {

    /* --- roots --- */
    int num_roots;
    printf("Enter number of roots: ");
    scanf("%d", &num_roots);
    int roots[MAX_NODES];
    printf("Enter roots: ");
    for (int i = 0; i < num_roots; i++) {
        scanf("%d", &roots[i]);
        roots[i] = get_id(roots[i]);
    }

    /* --- graph --- */
    int num_nodes, num_edges;
    printf("Enter number of nodes and edges: ");
    scanf("%d %d", &num_nodes, &num_edges);
    memset(deg, 0, sizeof(deg));
    printf("Enter edges: ");
    for (int i = 0; i < num_edges; i++) {
        int u, v;
        scanf("%d %d", &u, &v);
        u = get_id(u); v = get_id(v);
        adj[u][deg[u]++] = v;
    }

    /* --- red nodes (= accepting states QF) --- */
    int is_red[MAX_NODES];
    memset(is_red, 0, sizeof(is_red));
    int num_red;
    printf("Enter number of red nodes: ");
    scanf("%d", &num_red);
    printf("Enter red nodes: ");
    for (int i = 0; i < num_red; i++) {
        int r; scanf("%d", &r);
        is_red[get_id(r)] = 1;
    }

    /* -----------------------------------------------------------
     * Algorithm 2 state — flat flag arrays instead of sets.
     * in_open[v]        = 1  iff  v ∈ O
     * in_active[v]      = 1  iff  v ∈ A
     * in_interrupted[v] = 1  iff  v ∈ F
     * ----------------------------------------------------------- */
    int in_open[MAX_NODES],
        in_active[MAX_NODES],
        in_interrupted[MAX_NODES];
    int p[MAX_NODES];
    int any_open, any_interrupted;

    memset(in_open,        0, sizeof(in_open));
    memset(in_active,      0, sizeof(in_active));
    memset(in_interrupted, 0, sizeof(in_interrupted));
    for (int i = 0; i < num_nodes; i++) p[i] = BOTTOM;

    /* --- seed roots (Alg.2 lines 5-8) --- */
    for (int i = 0; i < num_roots; i++) {
        int r = roots[i];
        in_open[r] = 1;
        if (is_red[r]) { in_active[r] = 1; p[r] = r;       }
        else           {                    p[r] = EPSILON;  }
    }

    /* --- outer loop (Alg.2 line 9) --- */
    do {
        /* --- inner loop (Alg.2 lines 10-21) --- */
        for (int node = 0; node < num_nodes; node++) {
            if (!in_open[node]) continue;
            in_open[node] = 0;

            int alpha = p[node];

            for (int ci = 0; ci < deg[node]; ci++) {
                int child = adj[node][ci];

                /* line 13 — accepting cycle */
                if (alpha == child) {
                    printf("Detected an accepting cycle, "
                           "counter example found!\n");
                    return 0;
                }

                /* lines 14-17 — first visit to a red child */
                if (p[child] == BOTTOM && is_red[child]) {
                    in_active[child] = 1;
                    if (child > alpha)
                        alpha = child;              /* take over   */
                    else
                        in_interrupted[child] = 1;  /* 1st case    */
                }

                /* line 18 — atomic max update */
                int beta   = p[child];
                p[child]   = imax(alpha, beta);

                /* line 19 — 2nd interruption */
                if (alpha > beta && beta > EPSILON && in_open[child])
                    in_interrupted[beta] = 1;

                /* line 20 — 3rd interruption */
                if (beta > alpha && alpha > EPSILON && !in_active[child])
                    in_interrupted[alpha] = 1;

                /* line 21 — re-open child if p grew */
                if (alpha > beta)
                    in_open[child] = 1;
            }
        }

        /* --- post-processing (Alg.2 lines 22-28) --- */
        any_interrupted = 0;
        for (int v = 0; v < num_nodes; v++)
            if (in_interrupted[v]) { any_interrupted = 1; break; }

        if (any_interrupted) {
            for (int v = 0; v < num_nodes; v++) {
                if (in_active[v]) {
                    if (in_interrupted[v] && p[v] != v)
                        in_open[v] = 1;         /* reopen  */
                    else
                        in_active[v] = 0;       /* retire  */
                    in_interrupted[v] = 0;
                }
                /* line 28 — reset p */
                p[v] = in_active[v] ? v : EPSILON;
            }
        }

        any_open = 0;
        for (int v = 0; v < num_nodes; v++)
            if (in_open[v]) { any_open = 1; break; }

    } while (any_open);

    printf("No accepting cycle detected, no counter example found!\n");
    return 0;
}
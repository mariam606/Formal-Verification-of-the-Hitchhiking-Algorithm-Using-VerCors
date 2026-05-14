# Formal Verification of the Hitchhiking Algorithm in VerCors

This repository contains the formal verification of **Algorithm 2 (Hitchhiking)** from the paper [Hitching a Ride to a Lasso: Massively Parallel
On-The-Fly LTL Model Checking](hitchhiking-paper.pdf), implemented and verified using [VerCors](https://vercors.ewi.utwente.nl/) with PVL (Prototypal Verification Language).

## Background

The Hitchhiking algorithm detects accepting cycles in a graph. It operates on a directed graph in CSR (Compressed Sparse Row) format and uses three flag arrays to track state:

| Symbol | Array | Meaning |
|--------|-------|---------|
| O | `in_open` | Nodes still to be explored |
| A | `in_active` | Nodes in an active accepting search |
| F | `in_interrupted` | Nodes whose search was interrupted |

Special values for `p[v]`:

| Value | Constant | Meaning |
|-------|----------|---------|
| `-2` | `BOTTOM` | Node never reached |
| `-1` | `EPSILON` | Reached, but no accepting predecessor |
| `0..N-1` | — | ID of the maximal accepting predecessor |

## Repository Structure

```
.
├── hitchhiking.c        # Reference C implementation (executable, for testing)
├── hitchhiking.cpp      # Reference C++ implementation
├── hitchhiking.pvl      # Full VerCors-verified PVL version (final)
├── milestone1.pvl       # Skeleton — contract only, no body
├── milestone2.pvl       # Seed loop (Algorithm 2 lines 5–8)
├── milestone3.pvl       # Outer + inner loop structure (lines 9–11)
├── milestone4.pvl       # Child loop with full traversal logic (lines 12–21)
├── milestone5.pvl       # Complete algorithm with post-processing (lines 22–28)
├── milestone6.pvl       # First soundness condition: is_red[child] == 1 at return true
├── milestone7.pvl       # Second and third soundness conditions: there is a path from child to node and an edge from node to child at return true
└── README.md
```

## Verification Milestones

The PVL verification was developed incrementally. Each milestone builds on the previous one, adding more of the algorithm while keeping VerCors happy at each step.

### Milestone 1 — Skeleton (`milestone1.pvl`)
Establishes the full function contract (preconditions, permissions, CSR invariants) with an empty body. Verifies that the specification itself is well-formed.

### Milestone 2 — Seed Loop (`milestone2.pvl`)
Adds the initialization loop (Algorithm 2 lines 5–8) that seeds the open set `O` and the active set `A` from the root nodes.

### Milestone 3 — Outer + Inner Loop (`milestone3.pvl`)
Adds the outer `while (any_open)` loop and the inner node-scanning loop (lines 9–11). The child loop body is left as `assert true` (stubbed out).

### Milestone 4 — Child Loop (`milestone4.pvl`)
Fills in the child loop (lines 12–21): accepting cycle detection (early `return true`), first-visit handling of red nodes, atomic `p` update via `imax`, and the three interruption cases.

### Milestone 5 — Post-processing (`milestone5.pvl`)
Adds the post-processing phase (lines 22–28): checking whether `F` is non-empty, reopening interrupted active nodes, retiring others, and resetting `p`. This is the complete algorithm.

### Milestone 6 — First Soundness Condition (`milestone6.pvl`)
Begins the soundness proof by verifying the first condition: **when the algorithm returns `true`, the detected cycle node is red** (`assert is_red[child] == 1`). Two structural changes enable this:

1. `alpha` is moved inside the child loop (`int alpha = p[node]` declared fresh per iteration), so within any single iteration `alpha` always holds the current `p[node]` value.
2. A new child-loop invariant tracks that `alpha` always points to a red node when valid:
   ```pvl
   loop_invariant (0 <= alpha && alpha < num_nodes) ==> is_red[alpha] == 1;
   ```

### Milestone 7 — Second and third soundness conditions (`milestone7.pvl`)
Completes the soundness proof by introducing a ghost witness path and refactoring the contract for clarity.

**Ghost witness path:** Introduces `ghost seq<int>[] ghost_path`, wihch is a verification-only array where `ghost_path[v]` stores a witness path from `p[v]` to `v`. The following invariant is added to all 7 loops:
```pvl
loop_invariant (\forall int v; 0 <= v && v < num_nodes;
    (0 <= {:p[v]:} && p[v] < num_nodes) ==>
        |ghost_path[v]| >= 1 &&
        ghost_path[v][0] == p[v] &&
        ghost_path[v][|ghost_path[v]| - 1] == v &&
        (\forall int i; 0 <= i && i < |ghost_path[v]|;
            0 <= {:ghost_path[v][i]:} && ghost_path[v][i] < num_nodes) &&
        (\forall int i; 0 <= i && i < |ghost_path[v]| - 1;
            hasEdge(R, C, {:ghost_path[v][i]:}, ghost_path[v][i+1])));
```
This encodes four sub-invariants: the path starts at `p[v]`, ends at `v`, all nodes are in bounds, and every consecutive pair is a real graph edge.

**`hasEdge` pure function:** A pure function checks whether an edge exists in the CSR graph using an existential over column indices:
```pvl
requires 0 <= u && u < |R| - 1;
requires 0 <= R[u] && R[u+1] <= |C|;
pure bool hasEdge(seq<int> R, seq<int> C, int u, int v) =
    (\exists int j; R[u] <= j && j < R[u+1]; {:C[j]:} == v);
```
**Ghost path update:** The child loop updates `ghost_path` in two cases — case 1 must be checked first to avoid a self-loop aliasing bug:
- `p[child] == child` → `ghost_path[child] = [child]`
- `p[child] == p[node] && p[child] >= 0` → `ghost_path[child] = ghost_path[node] + [child]`

**Soundness assertions at `return true`:** Three assertions are verified when the accepting cycle is detected:
```pvl
assert is_red[child] == 1;
assert ghost_path[node][0] == child;
assert ghost_path[node][|ghost_path[node]| - 1] == node;
```
Together they witness: `child` is red, the path stored for `node` starts at `child` (i.e. `p[node] == child`), ends at `node`, consists only of valid nodes, and all consecutive pairs are real edges, and `node` has `child` as a successor (from `alpha == child`). This constitutes a complete witnessed accepting cycle.

**Cleanup:** Read-only inputs `roots`, `deg`, `is_red`, `R`, and `C` are changed from `int[]` to `seq<int>`, removing their `Perm` and null-check annotations. The magic numbers `-2` and `-1` are replaced by `BOTTOM()` and `EPSILON()` pure functions.

### Milestone 8 — Lemma 1: termination of each round (`milestone8.pvl`)

Proves **Lemma 1** from the paper: every time the main loop is entered and no counter-example is found, the loop eventually terminates (i.e., the open set O becomes empty). This required two changes relative to milestone 7.

**Structural refactoring — from flag to queue:** The `any_open` flag and full-node-scan inner loop (`while (node < num_nodes) { if (in_open[node] == 1) ... }`) are replaced by an explicit `seq<int> open_queue` and an integer `ptr`. Nodes are appended to the queue when first enqueued and `ptr` advances as they are dequeued. The outer loop becomes `while (ptr < |open_queue|)` and the inner loop (one round) is a nested `while (ptr < |open_queue|)`. The seed loop now also deduplicates roots (`if (in_open[r] == 0)`) before enqueuing. The end-of-round "recompute `any_open`" loop is eliminated — the queue handles termination detection.

**Termination proof — `decreases` clause:** A ghost variable `sum_p` tracks the total accumulated increase in p-values across all nodes. The termination measure is:
```pvl
decreases num_nodes * num_nodes - sum_p, |open_queue| - ptr;
```
This is a lexicographic pair: the primary component decreases as p-values increase (each p[v] can increase at most num_nodes times, so the sum is bounded by num_nodes²); the secondary component decreases as nodes are dequeued within a single round. Ghost snapshot variables `sum_p0` and `q0` are taken at the start of processing each node, and the invariant `sum_p - sum_p0 >= |open_queue| - q0` ensures that every new enqueue is accompanied by a p-value increase — preventing the queue from growing unboundedly without progress.

### Milestone 9 — Lemma 2: p ≠ BOTTOM for all enqueued nodes (`milestone9.pvl`)

Proves **Lemma 2** from the paper: once the first round completes, every reachable node has p ≠ ⊥ (BOTTOM), and this property is preserved for the rest of the execution. In the PVL encoding this is expressed as: every node ever placed in `open_queue` has `p ≠ BOTTOM()`.

**Lemma 2 invariant:** The following invariant is added to all 6 loops:
```pvl
loop_invariant (\forall int j; 0 <= j && j < |open_queue|;
    {:p[open_queue[j]]:} != BOTTOM());
```
It holds because: roots are enqueued with `p[r] = r` or `p[r] = EPSILON()`, both ≠ BOTTOM; children are enqueued only when `alpha > beta`, at which point `p[child]` has just been set to `alpha ≥ EPSILON() > BOTTOM()`; nodes re-enqueued during post-processing already had `p ≠ BOTTOM` from a prior enqueue. No write to `p` anywhere in the algorithm can produce BOTTOM.

### Milestone 10 — Lemma 3: max active node ≥ all p-values (`milestone10.pvl`)

Proves **Lemma 3** from the paper: if the active set A is non-empty, then for every node q̄ in the product state space, the maximum active node ID is at least p(q̄). In the PVL encoding this means: the historically largest node ever activated is an upper bound on all non-negative p-values.

**Ghost variable `max_active`:** A ghost integer tracks the maximum node ID ever placed into the active set across the entire execution:
```pvl
ghost int max_active = BOTTOM();
```
It is updated (and only ever increased) immediately after each `in_active[v] = 1` assignment — once in the seed loop and once in the child loop:
```pvl
ghost if (r > max_active) { max_active = r; }      // seed loop
ghost if (child > max_active) { max_active = child; } // child loop
```
The ghost update in the child loop is placed *before* the `if (child > alpha)` branch so that VerCors can derive `child <= max_active` sequentially when alpha is set to `child`, without needing an extra alpha invariant.

**Three new invariants added to all 6 loops:**
```pvl
loop_invariant max_active == BOTTOM() || (0 <= max_active && max_active < num_nodes);
loop_invariant (\forall int w; 0 <= w && w < num_nodes; {:p[w]:} >= 0 ==> p[w] <= max_active);
loop_invariant (\forall int v; 0 <= v && v < num_nodes; {:in_active[v]:} == 1 ==> v <= max_active);
```
The first is a bounds invariant. 

The second is Lemma 3 itself: any node with a non-negative p-value is ≤ max_active. 

The third invariant is a supporting lemma required specifically for the reset loop: when the reset loop sets `p[v] = v` for active nodes, VerCors needs to know `v <= max_active` to re-establish the Lemma 3 invariant.

The `max_active` is updated in the post-processing loop because some nodes are removed from the set of active nodes `in_active[]`.



## Running the Verifier

To verify any milestone with VerCors:

```bash
vct milestone5.pvl
```

Replace `milestone5.pvl` with whichever file you want to check.

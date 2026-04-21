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


## Running the Verifier

To verify any milestone with VerCors:

```bash
vct milestone5.pvl
```

Replace `milestone5.pvl` with whichever file you want to check.

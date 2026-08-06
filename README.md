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
├── milestone8.pvl       # Lemma 1 (completeness): termination of each round via open_queue refactoring and decreases clause
├── milestone9.pvl       # Lemma 2 (completeness): every enqueued node has p ≠ BOTTOM
├── milestone10.pvl      # Lemma 3 (completeness): max active node ID ≥ all p-values
├── milestone11.pvl      # Lemma 4 (completeness): if max_active is in an accepting cycle and all p ≠ BOTTOM, the algorithm returns true in the current round
├── milestone12.pvl      # Lemma 4 sub-properties: max_active is never interrupted; p[max_active] == max_active
├── milestone13.pvl      # Refactor: pure predicate bundles + decomposed helper functions (processRoots, resetActive, processNode)
├── milestone14.pvl      # Lemma 1 termination proof completed: sum_p assume replaced by a real potential-function proof
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
The first is a bounds invariant. The second is Lemma 3 itself: any node with a non-negative p-value is ≤ max_active. The implication form (`>= 0 ==>`) correctly excludes the sentinels BOTTOM(−2) and EPSILON(−1) without the vacuous-truth problem that arises with a conditional like `max_active >= 0 ==>`.

The third invariant is a supporting lemma required specifically for the reset loop: when the reset loop sets `p[v] = v` for active nodes, VerCors needs to know `v <= max_active` to re-establish the Lemma 3 invariant — and this is provided by `in_active[v] == 1 ==> v <= max_active`.

### Milestone 11 — Lemma 4: if max_active is in an accepting cycle, the algorithm detects it (`milestone11.pvl`)

Proves **Lemma 4** from the paper: *at the start of a round (l.9), if q̄_max ∈ C (the maximum active node is part of an accepting cycle) and ∀q̄ ∈ Q_⊗.p(q̄) ≠ ⊥ (all states have been reached, guaranteed by Lemma 2), then Hitchhiking returns a counter-example at l.13 before the round ends at l.22.*

**Contrapositive proof strategy:** Rather than proving the forward direction directly ("if max_active ∈ C then return true"), the PVL proof establishes the contrapositive: *if the algorithm has not returned `true`, then max_active is not in an accepting cycle.* Concretely, the invariant maintained throughout all loops is that no settled node (not in `open_queue`) whose `p`-value equals `max_active` has a completed accepting cycle as its ghost path. If such a path existed, the child loop would have detected the closing edge (`alpha == child`) and already triggered `return true` — a contradiction with the algorithm still running.

**`isCycle` pure function:** A new pure predicate checks whether a sequence of nodes forms a cycle in the CSR graph:
```pvl
requires 0 < |path|;
requires (\forall int i; 0 <= i && i < |path|; 0 <= path[i] && path[i] < |R| - 1);
requires (\forall int i; 0 <= i && i < |path|; 0 <= R[path[i]] && R[path[i] + 1] <= |C|);
pure bool isCycle(seq<int> path, seq<int> R, seq<int> C) =
    (\forall int i; 0 <= i && i < |path| - 1; hasEdge(R, C, path[i], path[i + 1])) &&
    hasEdge(R, C, path[|path| - 1], path[0]);
```
The three preconditions ensure the path is non-empty and all its nodes are in bounds so `hasEdge` can be called safely.

**Core `!isCycle` invariant added to all loops (seed, outer, middle, "check F", reset):**
```pvl
loop_invariant (\forall int v; 0 <= v && v < num_nodes;
    {:in_open[v]:} == 0 && 0 <= {:p[v]:} && {:p[v]:} == max_active ==>
    !isCycle(ghost_path[v], R, C));
```
This says: for every settled node (not in the open queue) whose parent pointer equals `max_active`, the recorded ghost path is not yet a cycle. The invariant is sound because the only way `ghost_path[v]` could become a cycle while `p[v] == max_active` is if there is an edge from `v` back to `max_active` — but the child loop checks exactly this condition (`alpha == child`) and returns `true` immediately when it holds.

**Child loop adaptation:** When `node` is being processed, it has already been removed from the open queue (`in_open[node] = 0`), but its successors are only partially scanned. The standard invariant cannot yet apply to `node` itself because the closing edge may not have been checked yet. It is therefore split into two parts:
```pvl
// For node: none of the already-scanned edges close a cycle back to max_active
loop_invariant 0 <= {:p[node]:} && {:p[node]:} == max_active && {:in_open[node]:} == 0 ==>
    (\forall int j; R[node] <= j && j < R[node] + ci; {:C[j]:} != max_active);
// For all other settled nodes: standard !isCycle invariant
loop_invariant (\forall int v; 0 <= v && v < num_nodes && v != node;
    {:in_open[v]:} == 0 && 0 <= {:p[v]:} && {:p[v]:} == max_active ==>
    !isCycle(ghost_path[v], R, C));
```
The first part is maintained because whenever `C[R[node] + ci] == max_active` and `p[node] == max_active`, the condition `alpha == child` fires and `return true` is reached — so the loop body is never entered in that case.

**Post-round assertion:** After the inner processing loop drains the queue, the invariant is re-asserted explicitly to confirm no cycle was missed in the completed round:
```pvl
assert (\forall int v; 0 <= v && v < num_nodes;
    {:in_open[v]:} == 0 && 0 <= {:p[v]:} && {:p[v]:} == max_active ==>
    !isCycle(ghost_path[v], R, C));
```

**Reset loop helper invariants:** The reset loop resets `p` and replaces `max_active` with a fresh `new_max`. To allow VerCors to re-establish the `!isCycle` invariant (now keyed on `new_max`) for the next round, three supporting invariants are added that describe the state of already-processed nodes (w < v):
```pvl
loop_invariant (\forall int w; 0 <= w && w < v; {:in_active[w]:} == 1 ==> {:in_open[w]:} == 1);
loop_invariant (\forall int w; 0 <= w && w < v; {:in_active[w]:} == 0 ==> {:p[w]:} == EPSILON());
loop_invariant (\forall int w; 0 <= w && w < v; {:in_open[w]:} == 0 ==> {:p[w]:} < 0);
loop_invariant (\forall int w; 0 <= w && w < v;
    {:in_open[w]:} == 0 && 0 <= {:p[w]:} && {:p[w]:} == new_max ==>
    !isCycle(ghost_path[w], R, C));
```
The first three helper invariants together make the fourth vacuously true for w < v: active nodes that remain active are re-enqueued (`in_open = 1`), so `in_open[w] == 0` is false; inactive nodes receive `p[w] = EPSILON() < 0`, so `0 <= p[w]` is false. This lets VerCors derive the `!isCycle` guard cannot be triggered for already-reset nodes, and the last invariant then holds for the new maximum `new_max`, which becomes `max_active` at the start of the next round.

### Milestone 12 — Lemma 4 sub-properties: max_active is never interrupted; new_max is always in the open set (`milestone12.pvl`)

Proves two invariant properties that support the completeness argument of Lemma 4:

1. **max_active is never interrupted**: `max_active >= 0 ==> in_interrupted[max_active] == 0` — the maximum active node is never placed in the interrupted set F.
2. **new_max is always in the open set**: `new_max >= 0 ==> in_open[new_max] == 1` — at the end of the reset loop, the candidate new maximum active node is already queued for the next round.

**Why max_active is never interrupted (ruling out all three interruption sites):**

`in_interrupted[v] = 1` is set in exactly three places in the child loop body:
- **Site 1** (`in_interrupted[child] = 1`): fires only when `p[child] == BOTTOM()`. But `p[max_active] == max_active ≠ BOTTOM()`, so max_active cannot be `child` here.
- **Site 2** (`in_interrupted[beta] = 1`): fires when `beta = p[child]` and `alpha > beta`. Since `alpha <= max_active` (from the Lemma 3 bound invariant) and `alpha > beta`, we get `beta < max_active`, so `beta ≠ max_active`.
- **Site 3** (`in_interrupted[alpha] = 1`): fires when `alpha = p[node] <= max_active` and `beta > alpha`. Since `beta > alpha`, `alpha < max_active`, so `alpha ≠ max_active`.

All three sites leave `in_interrupted[max_active]` untouched throughout the algorithm.

**Core invariants added to all loops:**
```pvl
loop_invariant max_active >= 0 ==> {:in_interrupted[max_active]:} == 0;
loop_invariant max_active >= 0 ==> {:p[max_active]:} == max_active;
```

The second invariant (`p[max_active] == max_active`) is needed to rule out Site 1: it guarantees that max_active's p-value is never BOTTOM, blocking the condition that triggers that site.

**Two auxiliary invariants required to close the Site 1 and Site 2 arguments:**
```pvl
// Rules out Site 1: a node with p == BOTTOM() was never interrupted
loop_invariant (\forall int v; 0 <= v && v < num_nodes;
    {:p[v]:} == BOTTOM() ==> {:in_interrupted[v]:} == 0);
// "Nested-p" invariant: if p[v] is a valid index, then p[p[v]] ≠ BOTTOM
loop_invariant (\forall int v; 0 <= v && v < num_nodes;
    0 <= {:p[v]:} && {:p[v]:} < num_nodes ==> {:p[p[v]]:} != BOTTOM());
```

The first says that interruptions and BOTTOM p-values are mutually exclusive. The second (the *nested-p invariant*) guarantees `beta = p[child] >= 0` implies `p[beta] ≠ BOTTOM()`, which is what VerCors needs to maintain the first invariant when Site 2 fires.

An assert hint in the child loop body makes `alpha <= max_active` visible to the solver at Site 2:
```pvl
assert max_active >= 0 ==> alpha <= max_active;
```

**Additional v loop invariants (for re-establishing these properties after the reset):**

The v loop rebuilds p-values from scratch, replacing `max_active` with `new_max`. Several invariants track the evolving `new_max` and the state of already-processed nodes (w < v):
```pvl
loop_invariant new_max >= 0 ==> new_max < v;
loop_invariant new_max >= 0 ==> {:in_open[new_max]:} == 1;
loop_invariant new_max >= 0 ==> {:in_active[new_max]:} == 1;
loop_invariant (\forall int w; 0 <= w && w < v; {:in_active[w]:} == 1 ==> {:p[w]:} == w);
loop_invariant (\forall int w; 0 <= w && w < v; {:in_active[w]:} == 0 ==> {:p[w]:} == EPSILON());
loop_invariant (\forall int w; 0 <= w && w < v; {:p[w]:} != BOTTOM());
```

`new_max < v` tells VerCors that `new_max` is always an already-processed node, so deactivating the current node v cannot affect `in_active[new_max]`. Combined with `in_active[w] == 1 ==> p[w] == w`, VerCors can derive `p[new_max] == new_max` at loop exit, which re-establishes `p[max_active] == max_active` after `ghost max_active = new_max`.

### Milestone 13 — Refactor: pure predicate bundles and decomposed helper functions (`milestone13.pvl`)

This milestone is a pure refactor of milestone 12 — no new lemma is proved. The single ~470-line `hitchhiking` body, with its five nested loops each repeating the same ~20-line block of `loop_invariant`s verbatim, is restructured into small reusable pure predicates and four standalone helper functions. The goal is maintainability: the same state properties are now stated once and reused everywhere, instead of being copy-pasted per loop.

**Predicate bundling.** The invariant block that used to be duplicated across every loop is factored into named `inline pure bool` predicates, each covering one concern:
```pvl
inline pure bool flags01(int[] a, int n) =
    (\forall int v; 0 <= v && v < n; {:a[v]:} == 0 || a[v] == 1);

inline pure bool pWellFormed(int[] p, seq<int> is_red, int n) = ...      // p in range, red predecessor
inline pure bool activeImpliesRed(int[] in_active, seq<int> is_red, int n) = ...
inline pure bool queueOk(seq<int> q, int[] p, int n) = ...               // queued nodes in range, p != BOTTOM
inline pure bool ghostPathsOk(int n, seq<int> R, seq<int> C, seq<int>[] ghost_path, int[] p) = ...
inline pure bool maxActiveOk(int[] p, int[] in_active, int m, int n) = ... // Lemma 3 bound
```
These are composed into a single umbrella predicate, `stateInv`, which is what every loop now states as its invariant:
```pvl
inline pure bool stateInv(int n, seq<int> R, seq<int> C, seq<int> is_red, seq<int> q,
                          int[] p, int[] in_active, seq<int>[] ghost_path, int m) =
    queueOk(q, p, n) &&
    pWellFormed(p, is_red, n) &&
    activeImpliesRed(in_active, is_red, n) &&
    ghostPathsOk(n, R, C, ghost_path, p) &&
    maxActiveOk(p, in_active, m, n);
```
Likewise, the repeated `context_everywhere` blocks (graph well-formedness, array lengths, root bounds) are bundled into `validGraph`, `validInput`, and `validRoots`, and the repeated "all zero / all BOTTOM" initial-state requires-clauses are captured by a generic `allEq(a, n, val)` helper.

**Function decomposition.** The four algorithm phases are pulled out into their own top-level PVL methods, each with its own contract expressed in terms of `stateInv`:
- `anyInterrupted` — the "is F non-empty?" check (previously an inline scan loop).
- `processRoots` — the seed loop (lines 5–8), returns the initial `open_queue`.
- `processNode` — the child loop (lines 12–21), including the accepting-cycle check.
- `resetActive` — the post-processing loop (lines 22–28).

Because ghost state (`max_active`, `sum_p`) and the discovered cycle now need to cross function-call boundaries instead of just loop-iteration boundaries, these are threaded using VerCors' `given`/`yields` mechanism:
```pvl
open_queue = processRoots(num_nodes, num_roots, roots, is_red, R, C,
                           p, in_open, in_active, ghost_path)
             yields { max_active = max_active_out };
...
open_queue = processNode(num_nodes, is_red, R, C, node, open_queue,
                         p, in_open, in_active, in_interrupted, found, ghost_path)
             given  { sum_p_in = sum_p, max_active_in = max_active }
             yields { sum_p = sum_p_out, max_active = max_active_out, cycle = cycle_out };
```
Since `processNode` is called from inside a loop in `hitchhiking` and can no longer `return true` directly up through the caller, cycle detection is instead signalled through a shared heap cell `int[] found`, checked by the caller after each call: `if (found[0] == 1) { return true; }`.

**Stronger accepting-cycle definition.** The old `isCycle` (a bare graph-cycle check, with redness verified separately via a standalone assertion) is replaced by two composed predicates that match the paper's definition directly:
```pvl
inline pure bool isAPath(int N, seq<int> R, seq<int> C, seq<int> path) =
    |path| > 0 &&
    (\forall int i; 0 <= i && i < |path|; 0 <= {:path[i]:} && path[i] < N) &&
    (\forall int i; 0 <= i && i < |path| - 1; isEdge(R, C, {:path[i]:}, path[i+1]));

inline pure bool isAcceptingCycle(int N, seq<int> R, seq<int> C, seq<int> is_red, seq<int> path) =
    isAPath(N, R, C, path) &&
    isEdge(R, C, path[|path| - 1], path[0]) &&
    (\exists int i; 0 <= i && i < |path|; is_red[{:path[i]:}] == 1);
```
`isAcceptingCycle` is now used directly in the postconditions of both `processNode` and `hitchhiking`: `ensures found[0] == 1 ==> isAcceptingCycle(...)` / `ensures \result ==> isAcceptingCycle(...)`. `hasEdge` is renamed `isEdge`, and the redundant `deg` seq (previously carried alongside `R` with an invariant tying it to `R[u+1] - R[u]`) is dropped — degree is now computed on demand via `inline pure int degree(seq<int> R, int u) = R[u+1] - R[u];`.

**Scope note.** `stateInv` currently bundles only the Lemma 1–3 level invariants (queue well-formedness, `p` well-formedness, active⇒red, ghost-path witnesses, and the Lemma 3 max-active bound). The Lemma 4-specific invariants added in milestones 11–12 — the `!isCycle` non-interruption invariant, `in_interrupted[max_active] == 0`, `p[max_active] == max_active`, and the nested-`p` invariant — are not carried forward into this refactor. Re-establishing Lemma 4 on top of the new modular structure is left for a later milestone.

### Milestone 14 — Lemma 1 termination proof completed: real potential function instead of `assume` (`milestone14.pvl`)

Since Milestone 8, the termination proof for Lemma 1 rested on one unproved gap: the child loop's atomic `p`-update contained `assume sum_p_out <= num_nodes * num_nodes;` — asserting the bound the `decreases` clause needs, without ever proving it. This milestone replaces that `assume` with an actual proof, built from scratch since VerCors has no built-in way to reason about "the sum of an array."

**Bound correction: `num_nodes * num_nodes` → `num_nodes * (num_nodes + 1)`.** `sum_p_out` accumulates `alpha - beta` every time `p[child]` jumps from `beta` to `alpha`; for a fixed node these increments telescope to `(final value) - (initial value)`. The catch: a node's initial value for this measure can be `BOTTOM()` (`-2`), not `0`, so a single node's contribution is bounded by `(num_nodes - 1) - BOTTOM() = num_nodes + 1`, not `num_nodes - 1`. Summed over `num_nodes` nodes, the provable bound is `num_nodes * (num_nodes + 1)`. The constant is updated everywhere it appears (`processNode`, `resetActive`, and the `hitchhiking` loop invariants/`decreases` clause) — the exact value doesn't matter for correctness, only that it's an honest, provable bound.

**Potential-function machinery — `prefixSum` and `lemma_prefixSum_update`:**
```pvl
requires 0 <= k && k <= |xs|;
requires (\forall int i; 0 <= i && i < |xs|; BOTTOM() <= xs[i] && xs[i] < n);
ensures 0 <= \result;
ensures \result <= k * (n - BOTTOM() - 1);
decreases k;
pure int prefixSum(seq<int> xs, int k, int n) =
    k == 0 ? 0 : prefixSum(xs, k - 1, n) + (xs[k - 1] - BOTTOM());

ensures k <= idx ==> prefixSum(xs[idx -> v], k, n) == prefixSum(xs, k, n);
ensures k > idx ==> prefixSum(xs[idx -> v], k, n) == prefixSum(xs, k, n) - xs[idx] + v;
decreases k;
void lemma_prefixSum_update(seq<int> xs, int idx, int v, int k, int n) {
    if (k == 0) {
    } else {
        lemma_prefixSum_update(xs, idx, v, k - 1, n);
    }
}
```
`prefixSum` is the formal potential: the sum of `xs[i] - BOTTOM()` over the first `k` slots, shifted so a slot still at `BOTTOM()` contributes `0`. Its own `ensures` gives the bound for free. `lemma_prefixSum_update` proves the one fact VerCors cannot derive automatically: that overwriting a single slot shifts this recursive sum by exactly that slot's delta. VerCors does not unfold a recursive definition more than one level on its own, so this has to be proved by explicit induction, recursing in lockstep with `prefixSum`'s own recursion so each step only needs one level of unfolding.

**Base-case machinery — `allBottomSeq`, `lemma_prefixSum_congruent`, `lemma_allBottom_sum_zero`:**
```pvl
pure seq<int> allBottomSeq(int n) =
    n == 0 ? seq<int>{} : allBottomSeq(n - 1) + seq<int>{BOTTOM()};

ensures prefixSum(xs, k, n) == prefixSum(ys, k, n);   // when xs, ys agree on their first k elements
void lemma_prefixSum_congruent(seq<int> xs, seq<int> ys, int k, int n) { ... }

requires 0 <= m && m <= n;
ensures prefixSum(allBottomSeq(m), m, n) == 0;
decreases m;
void lemma_allBottom_sum_zero(int m, int n) {
    if (m == 0) {
    } else {
        lemma_allBottom_sum_zero(m - 1, n);
        lemma_prefixSum_congruent(allBottomSeq(m), allBottomSeq(m - 1), m - 1, n);
    }
}
```
Before any node is discovered, `p[]` is all `BOTTOM()`, and the potential should start at `0` — but `prefixSum(allBottomSeq(num_nodes), ...) == 0` needs its own induction, chaining two recursive definitions together. `lemma_allBottom_sum_zero` proves it. It deliberately keeps `m` (the shrinking recursion variable) separate from `n` (the fixed range cap `prefixSum` needs): recursing on a single shared parameter would leave the induction hypothesis talking about `prefixSum(allBottomSeq(m-1), m-1, m-1)` instead of the needed `prefixSum(allBottomSeq(m-1), m-1, n)` — same value, but a different term to the verifier. `lemma_prefixSum_congruent` (agreeing sequences on a prefix ⟹ agreeing prefix sums) is the bridge that transfers the induction hypothesis, proved about `allBottomSeq(m-1)`, onto the first `m-1` slots of the longer `allBottomSeq(m)`.

**Ghost mirror `p_seq`, threaded via `given`/`yields`.** `prefixSum` needs an *immutable* value to recurse over when comparing "before" and "after" a write — an `int[]` array can't serve that role, since once `p[child]` is overwritten, its old content is simply gone (there's no persistent second copy of the array to compare against). So every method that writes `p[]` — `processRoots`, `processNode`, `resetActive` — now also carries a ghost `seq<int> p_seq` that mirrors `p[]` value-for-value, plus `sum_p`/`sum_p_out` defined to literally equal `prefixSum(p_seq, num_nodes, num_nodes)` (not just bounded by it). At every real write, the pattern is:
```pvl
ghost seq<int> p_seq_before = p_seq_out;
p[child] = imax(alpha, beta);
ghost p_seq_out = p_seq_out[child -> p[child]];
lemma_prefixSum_update(p_seq_before, child, p[child], num_nodes, num_nodes);
ghost if (alpha > beta) { ghost sum_p_out = sum_p_out + alpha - beta; }
```
The lemma hands VerCors the exact relation between the old and new potential, which lines up with the plain arithmetic update on the last line, so the invariant `sum_p_out == prefixSum(p_seq_out, ...)` survives every write.

**`resetActive` also writes `p[]`.** Tracing through the proof surfaced that `resetActive`'s reset loop (lines 22–28 of the algorithm) unconditionally sets `p[v] = v` or `p[v] = EPSILON()` on every node — a real change to `p[]`, not a no-op — so it needed the identical `p_seq`/`sum_p` treatment as `processRoots` and `processNode`. Unlike those two, `resetActive`'s update is not monotonic (`p[v]` can move down as well as up), which is fine: `lemma_prefixSum_update` proves an exact equality regardless of direction, and a shrinking `sum_p` only makes its upper bound easier to satisfy.

**Per-epoch potential reset removed.** Milestone 8 reset `ghost int sum_p = 0;` at the top of every outer-loop iteration, treating `sum_p` as "growth since this round started." That stops making sense once `sum_p` is defined to literally equal the current `prefixSum(p_seq, ...)` — resetting it to `0` while `p[]` still holds everything accumulated from earlier rounds would falsify the invariant outright. `sum_p` is now declared once, right after `processRoots` runs, and carried for the whole method without ever resetting.

## Running the Verifier

To verify any milestone with VerCors:

```bash
vct milestone5.pvl
```

Replace `milestone5.pvl` with whichever file you want to check.

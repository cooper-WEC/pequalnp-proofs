# A 63-gate witness for L-meta-650 needs nested AND gates

PlaneIncidence.lean proves that a 64-gate monotone circuit computes the exact posted function for every assignment. The 13 point terms each use three OR gates to combine their incident lines and one AND gate to test the point. Twelve more OR gates combine the terms. Lean verifies the wire indices, the gate count and the symbolic Boolean identity.

## Optimality with at most one AND per path

Here is a pencil-and-paper lower bound, allowing arbitrary fan-out. Simplify away constants, copies, unused gates, and redundant one-input ORs. Each live AND takes two ORs of sets of inputs (a single input is also allowed). Every path above this AND consists entirely of ORs. Consequently every pair from the two input sets must be an edge, and the sets must be disjoint since singletons are rejected. A raw input cannot reach the output along a path consisting entirely of ORs, for the same reason.

The incidence graph has no 4-cycle, so each of these complete bipartite subgraphs is a star. Choose either endpoint as center for a one-edge star. Let t be the number of live AND gates, and d the number of distinct centers. All 52 edges must be covered, and each AND covers at most four, giving t ≥ 13.

Let q count the OR gates below the AND gates. For each center c, combine its leaf sums into a single OR with support S_c. Across all centers this costs at most t − d extra ORs. For distinct centers, the sets S_c share at most one input, since two common neighbors would give a 4-cycle. An intermediate OR with support of size at least two can therefore serve at most one of the resulting sums. For a sum on k distinct inputs, at least k − 1 such gates are needed. Indeed, contract wires that only copy one input and count the edges of the connected fan-in-two graph producing the sum. Thus

    q + t − d ≥ Σ_c (|S_c| − 1) ≥ 52 − d.

The last inequality counts every graph edge at least once. At least t − 1 additional ORs combine the t AND outputs. These ORs are disjoint from the q earlier ORs because an AND-to-AND path is forbidden. The total size is at least q + t + (t − 1) ≥ 52 + t − 1 ≥ 64.

This leaves the nested-AND case of the posted problem open. For background on single-level circuits and biclique covers, see [Jukna, Disproving the Single Level Conjecture, §3.5](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf).

Run the Lean check from the project's lean directory with lake env lean followed by the path to PlaneIncidence.lean. The helper for peeling one edge off the list adapts the repository's L-meta-587 proof.

# AND-gate bounds for L-meta-632

The assignment tests a circuit on each maximal independent set I of a graph and on each set obtained by adding one vertex to I. It must reject I and accept each extension. OR is free.

PartialCover.lean proves the following results in the project's circuit model.

| Lean theorem | Result |
| --- | --- |
| upper | Every finite graph has a well-formed passing circuit with at most as many AND gates as any vertex cover. This proves the first conjunct of the posted statement, without a girth assumption. |
| counting_bound | For a passing circuit with k AND gates, every family of distinct maximal independent sets has size at most 2^k. |
| matching_exact | For m disjoint edges the minimum is m, including m = 0. |
| windmill_exact | For m triangles sharing a single hub, with m positive, the minimum is m + 1. |

For the counting bound, label an input by the k-bit vector of left-side truth values at its AND gates. Suppose two rejected inputs have the same label. At each gate that is true on their union, one constituent input already makes the gate true. To see this, induct in gate order. Each OR side that becomes true on the union is true on some constituent. The common label then makes the left side true on both, so the constituent witnessing the right side witnesses the entire gate. The same argument at the output shows that the union is rejected. Distinct maximal independent sets cannot have the same label: their union contains an accepted single-vertex extension of one of them, and the circuit is monotone.

For the matching, selecting one end of each edge gives 2^m maximal independent sets. The windmill has these same 2^m rim selections and the additional singleton containing the hub. A cover with one vertex per pair, plus the hub in the windmill, attains each lower bound.

The general converse, extracting a cover no larger than an arbitrary passing circuit on a graph without a four-cycle, remains open. The counting bound alone can fall short. For example, the five-cycle has five maximal independent sets and minimum cover size three, while the disjoint union of three five-cycles has 125 maximal independent sets and minimum cover size nine; counting gives only seven there.

Checked against project commit bb99fb9. From the lean directory run lake env lean followed by the path to PartialCover.lean. All four listed theorems use only propext, Classical.choice and Quot.sound.

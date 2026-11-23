# L-meta-586 requires exactly eight OR gates

The graph has the edge 01 and the two paths 12340 and 15670. A monotone circuit can AND the endpoints of each of its nine edges and OR the nine results using eight binary OR gates. The three certificate checks below exclude a circuit with at most seven binary OR gates, allowing arbitrarily many AND gates.

## Circuit representation

Order the OR gates topologically. Each of their two arms is a conjunction of a subset of the eight inputs and earlier OR outputs. The final output is another such conjunction. This follows by flattening every AND between OR gates. Constant false can be propagated away because the function is nonconstant. Empty conjunctions represent true, repeated factors can be removed, and unused OR slots allow padding. This covers unary and nullary gates and the project's default-false out-of-range wires.

The selector bits for each conjunction are shared across all assignments. Its value on a row is true exactly when no selected wire is false. Only edge pairs and maximal independent sets need evaluation. Every positive assignment contains an edge pair and every negative assignment lies inside a maximal independent set.

## Two smaller instances

Fix a degree-two vertex v to zero. There are two types up to swapping the two length-four paths and reversing both paths together. Deleting vertex 2 represents 2, 4, 5, 7. Deleting vertex 3 represents 3, 6. In each case the direct five-OR encoding is unsatisfiable. The deleted input remains available as an irrelevant variable in the search. Thus every restricted graph needs at least six OR gates.

## Constraints for the full graph

Call a wire forced if it always vanishes when v is zero. Monotonicity lets us test this at the assignment with all other inputs true. A conjunction is forced exactly when it selects a forced factor. An OR is forced exactly when both arms are forced.

An OR with at least one forced arm disappears when v is fixed to zero. Two such ORs would leave at most five, contradicting the verified restriction bound. There must be at least one. Otherwise every nonforced wire is independent of v, by induction through the circuit. The output is nonforced because the graph has an edge avoiding v, yet it depends on v.

Let h be this unique OR. Replacing h by a fresh independent input makes every originally nonforced wire a function of the other seven inputs and the fresh input. This follows by induction, treating h as a new input at its position. A nonforced conjunction has only nonforced factors, and every other OR has two nonforced arms. In particular, whenever flipping v changes the target, h must also change. Monotonicity fixes the direction. Therefore h is true on every edge pair incident to v and false on every maximal independent set that acquires an edge when v is added. The full seven-OR encoding imposes precisely these necessary restriction constraints, in addition to the circuit and output equations. Its certificate also verifies.

## Reproduction

Run with Python 3, CaDiCaL and the independent lrat-check executable from marijnheule/drat-trim. CaDiCaL returns exit code 20 for each instance. lrat-check prints VERIFIED for each certificate.

```sh
python3 encode.py --delete 2 > delete2.cnf
python3 encode.py --delete 3 > delete3.cnf
python3 encode.py > full.cnf
for instance in delete2 delete3 full
do
    cadical -q --lrat --no-binary "$instance.cnf" "$instance.lrat" || test "$?" = 20 || exit 1
    lrat-check "$instance.cnf" "$instance.lrat" || exit 1
done
```

| Instance | Variables | Clauses | DIMACS SHA-256 |
| --- | ---: | ---: | --- |
| delete2 | 2168 | 7305 | 4f3571d30c18205f310bc4bdcc0dedafb5e2bcc267a1964ff35c743147d56707 |
| delete3 | 1894 | 6331 | 5ceb00fbd28e4c38d6f11e5a9bc93e53c791fd83dcd7ef32aabb7c61115c6dba |
| full | 4569 | 16344 | f5a8184bfa4b933bddfd27428a604be35440d4e8717339718f0b2bb4f1901d8c |

The LRAT certificates establish unsatisfiability of the generated formulas. The reduction from the posted circuit statement is given above in prose.

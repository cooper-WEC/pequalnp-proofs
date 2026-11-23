"""Write the DIMACS instance for L-meta-586 or one of its two restrictions."""

import argparse
from itertools import combinations

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--delete", type=int, choices=(2, 3))
args = parser.parse_args()

edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
         (1, 5), (5, 6), (6, 7), (7, 0)]
edges = [edge for edge in edges if args.delete not in edge]


def target(mask):
    return any((mask >> i) & (mask >> j) & 1 for i, j in edges)


# For a monotone function the minimal true and maximal false rows suffice.
rows = [mask for mask in range(256)
        if all(target(mask) != target(mask ^ (1 << i))
               for i in range(8) if ((mask >> i) & 1) == target(mask))]
clauses = []
variable_count = 0


def fresh():
    global variable_count
    variable_count += 1
    return variable_count


def both(a, b):
    out = fresh()
    clauses.extend([[-out, a], [-out, b], [out, -a, -b]])
    return out


def disjoin(literals):
    out = fresh()
    clauses.append([-out] + literals)
    clauses.extend([[out, -lit] for lit in literals])
    return out


def conjunction(wires):
    """Choose a subset of available wires, shared across all truth-table rows."""
    selected = [fresh() for _ in wires]
    values = []
    for row in range(len(rows)):
        value = fresh()
        failures = []
        for select, wire in zip(selected, wires):
            failure = fresh()
            bit = wire[row]
            clauses.extend([[-failure, select], [-failure, -bit],
                            [failure, -select, bit], [-value, -failure]])
            failures.append(failure)
        clauses.append([value] + failures)
        values.append(value)
    return selected, values


wires = [[fresh() for _ in rows] for _ in range(8)]
for i, wire in enumerate(wires):
    for val, mask in zip(wire, rows):
        clauses.append([val if (mask >> i) & 1 else -val])

gates = []
for _ in range(7 if args.delete is None else 5):
    left_select, left = conjunction(wires)
    right_select, right = conjunction(wires)
    output = [fresh() for _ in rows]
    for a, b, c in zip(left, right, output):
        clauses.extend([[-a, c], [-b, c], [a, b, -c]])
    gates.append((left_select, right_select))
    wires.append(output)


def constrain_restriction(vertex):
    # forced[i] says wire i vanishes whenever vertex is false.
    forced = [None] * 8
    releases = []

    def arm_vanishes(selected):
        return disjoin([selected[vertex]] +
                       [both(selected[i], forced[i]) for i in range(8, len(selected))])

    for k, (left, right) in enumerate(gates):
        a, b = arm_vanishes(left), arm_vanishes(right)
        release = disjoin([a, b])
        releases.append(release)
        forced.append(both(a, b))
        for j, mask in enumerate(rows):
            if target(mask) and (mask >> vertex) & 1:
                clauses.append([-release, wires[8 + k][j]])
            if not target(mask) and not ((mask >> vertex) & 1) and target(mask | (1 << vertex)):
                clauses.append([-release, -wires[8 + k][j]])
    clauses.append(releases)
    clauses.extend([[-a, -b] for a, b in combinations(releases, 2)])


if args.delete is None:
    for vertex in (2, 3, 4, 5, 6, 7):
        constrain_restriction(vertex)

_, outputs = conjunction(wires)
for value, mask in zip(outputs, rows):
    clauses.append([value if target(mask) else -value])
print("p cnf", variable_count, len(clauses))
for clause in clauses:
    print(*clause, 0)

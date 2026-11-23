"""Certify that three six-dimensional spaces in the 4 by 5 problem are maximal."""
from hashlib import sha256
from itertools import permutations
from math import prod

P = 241
omega = next(t for t in range(2, P) if (t * t + t + 1) % P == 0)
injections = [tuple(5 * i + j for i, j in enumerate(columns))
              for columns in permutations(range(5), 4)]


def basis_point(family, z):
    a, b, c, d, e, h = z
    if family == "L-gct-180":
        return [a, -a, b, -b, 0,
                omega*a, -omega*a, omega**2*b, -omega**2*b, 0,
                omega**2*a, -omega**2*a, omega*b, -omega*b, 0,
                c, d, e, h, -c-d-e-h]
    if family == "zero-sum row":
        return [a, b, c, d, -a-b-c-d,
                e, 0, 0, 0, 0, h, 0, 0, 0, 0, -e-h, 0, 0, 0, 0]
    return [-a-b-c, d, e, h, -d-e-h,
            a, 0, 0, 0, 0, b, 0, 0, 0, 0, c, 0, 0, 0, 0]


def permanent(t):
    return sum(prod(1+t[j] for j in f) for f in injections) % P


def gradient(t):
    row = [0] * 20
    for f in injections:
        for i in f:
            row[i] += prod(1+t[j] for j in f if j != i)
    return [x % P for x in row]


def certify(family):
    echelon = {}
    selected = []
    for sample in range(100):
        z = list(sha256(str(sample).encode()).digest()[:6])
        point = basis_point(family, z)
        assert permanent(point) == 120
        row = gradient(point)
        for i, pivot in sorted(echelon.items()):
            multiplier = row[i]
            row = [(x - multiplier*y) % P for x, y in zip(row, pivot)]
        if any(row):
            i = next(i for i, value in enumerate(row) if value)
            echelon[i] = [v * pow(row[i], -1, P) % P for v in row]
            selected.append(point)
        if len(selected) == 13:
            break
    assert len(echelon) == 13
    for free in sorted(set(range(20)) - echelon.keys()):
        direction = [int(j == free) for j in range(20)]
        for i, row in sorted(echelon.items(), reverse=True):
            direction[i] = -sum(a*b for a, b in zip(row, direction)) % P
        assert all(sum(a*b for a, b in zip(gradient(t), direction)) % P == 0
                   for t in selected)
        value = permanent(direction)
        if value != 120:
            print(f"{family}: 13 independent gradients; F(kernel vector) = {value} mod {P}")
            return
    raise ValueError("No certificate found")


for name in ("L-gct-180", "zero-sum row", "zero-sum column"):
    certify(name)

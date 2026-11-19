"""Exact Bernstein proof of the flat-four-tail rank-seven comparison."""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import comb, lcm

from verify_rank7_residual_single_probe import add_scaled, multiply


RAYS = ((1, 0), (1, F(1, 2)), (1, 1), (1, 2), (0, 1))
GEOMETRY = F(5, 2)
SHIFT = F(5, 4)
EXTERIOR_RATE = 168 * F(101, 100)
RESIDUAL = 1 - 24 * SHIFT / EXTERIOR_RATE
SQUARE = 12 * (2 * SHIFT - SHIFT**2)
SHARED = (SQUARE + 1) / (12 * EXTERIOR_RATE)
HIGHEST = SQUARE / (GEOMETRY * EXTERIOR_RATE)
BOUND = 33


def sum_polynomials(*terms):
    result = Counter()
    for scale, polynomial in terms:
        add_scaled(result, polynomial, scale)
    return result


def objectives(n, v):
    """Return the base and two alternate signed-cut numerators."""
    h, k, q = ({(i,): F(BOUND, i + 1)} for i in range(3))
    one = {(): 1}
    x = sum_polynomials((1, h), (1, k), (1, q))
    y = sum_polynomials((1, k), (1, q))
    alpha = sum_polynomials((1, x), (1, one))
    beta = sum_polynomials((1, y), (1, one))
    gamma = sum_polynomials((1, q), (1, one))
    g = multiply(h, q)
    delta = multiply(k, x)
    f = multiply(x, y, q)
    anticommuting = multiply(k, k, sum_polynomials(
        (1, multiply(k, k)), (F(1, 2), multiply(h, h)), (F(1, 2), multiply(q, q)),
    ))
    m = max(n, F(v) / 2)
    z = max(F(5, 2) * n, 2 * v, 2 * n + v)
    base = sum_polynomials(
        (m, h), (2 * m, k), (3 * m, q), (z, one),
        (SHARED * max(n, v), multiply(g, g)),
        (HIGHEST * v, multiply(delta, delta)),
        (v / (GEOMETRY * EXTERIOR_RATE), anticommuting),
        (-RESIDUAL * n, g), (-RESIDUAL * v, delta),
    )
    top_denom = sum_polynomials((1, beta), (1, gamma))
    base_numerator = sum_polynomials(
        (1, multiply(top_denom, base)), (32 * v / EXTERIOR_RATE, multiply(alpha, k, k)),
    )
    if not n:
        return [base_numerator]

    # The inside squared amplitude is alpha*gamma. The outside maximum
    # is either alpha or beta*gamma. The first signed price cancels q.
    signed = sum_polynomials((1, f), (-F(1, 3), delta))
    outer_alpha_denom = multiply(
        sum_polynomials((2, one), (1, q)),
        sum_polynomials((1, h), (2, multiply(x, y))),
    )
    outer_beta_denom = multiply(
        sum_polynomials((1, alpha), (1, beta)), sum_polynomials((1, g), (2, f)),
    )
    return [
        base_numerator,
        sum_polynomials(
            (1, multiply(base_numerator, outer_alpha_denom)),
            (48 * n / EXTERIOR_RATE, multiply(top_denom, alpha, q, signed)),
        ),
        sum_polynomials(
            (1, multiply(base_numerator, outer_beta_denom)),
            (48 * n / EXTERIOR_RATE, multiply(top_denom, gamma, h, h, signed)),
        ),
    ]


@dataclass(frozen=True)
class Grid:
    degrees: tuple
    blocks: tuple
    values: tuple

    @property
    def nonnegative(self):
        return min(self.values) >= 0

    def halves(self, axis):
        degree = self.degrees[axis]
        left = [0] * len(self.values)
        right = [0] * len(self.values)
        for indices in self.blocks[axis]:
            line = [self.values[i] for i in indices]
            left[indices[0]] = line[0] << degree
            right[indices[-1]] = line[-1] << degree
            for order in range(1, degree + 1):
                line = [lo + hi for lo, hi in zip(line, line[1:])]
                left[indices[order]] = line[0] << (degree - order)
                right[indices[-order - 1]] = line[-1] << (degree - order)
        return Grid(self.degrees, self.blocks, tuple(left)), Grid(self.degrees, self.blocks, tuple(right))


def bernstein_grid(polynomial, dimension=3):
    powers = [(tuple(m.count(i) for i in range(dimension)), F(c))
              for m, c in polynomial.items() if c]
    degrees = tuple(max(m[i] for m, _ in powers) for i in range(dimension))
    keys = list(product(*(range(n + 1) for n in degrees)))
    positions = {key: i for i, key in enumerate(keys)}
    blocks = tuple(tuple(
        tuple(positions[key[:axis] + (j,) + key[axis + 1:]] for j in range(degree + 1))
        for key in keys if key[axis] == 0
    ) for axis, degree in enumerate(degrees))
    # Each tensor transform is scaled by one positive integer to keep
    # subsequent arithmetic integral. The common factor is irrelevant.
    scale = lcm(*(v.denominator for _, v in powers))
    values = [0] * len(keys)
    for key, coefficient in powers:
        values[positions[key]] = int(coefficient * scale)
    for axis, degree in enumerate(degrees):
        denominator = lcm(*(comb(degree, j) for j in range(degree + 1)))
        matrix = [
            [comb(i, j) * (denominator // comb(degree, j)) for j in range(i + 1)]
            for i in range(degree + 1)
        ]
        for indices in blocks[axis]:
            line = [values[i] for i in indices]
            for index, row in zip(indices, matrix, strict=True):
                values[index] = sum(c * x for c, x in zip(row, line))
    return Grid(degrees, blocks, tuple(values))


def verify_outer(ray):
    n, v = ray
    # Complete squares in g and Delta. R >= Delta^2/5 by Cauchy--Schwarz.
    if not (RESIDUAL**2 < 4 * SHARED * 29 and
            RESIDUAL**2 < 4 * (HIGHEST + 1 / (5 * GEOMETRY * EXTERIOR_RATE)) * 7):
        raise ArithmeticError("Invalid square envelope")
    m = max(n, F(v) / 2)
    z = max(F(5, 2) * n, 2 * v, 2 * n + v)
    if BOUND * m + z < F(29 * n * n, max(n, v)) + 7 * v:
        raise ArithmeticError("Invalid outer region")


def verify_outer_perturbation():
    tail_ratio = F(101, 100)
    shared_loss = F(200, 11) * tail_ratio * (tail_ratio - 1)
    shared_linear = tail_ratio * RESIDUAL + F(15, 4) * shared_loss / EXTERIOR_RATE
    shared_constant = tail_ratio * 30 * shared_loss / EXTERIOR_RATE
    if not (shared_linear**2 < 4 * SHARED * 30 and shared_constant < F(1, 20)):
        raise ArithmeticError("Invalid perturbed square envelope")
    for n, v in RAYS:
        m = max(n, F(v) / 2)
        z = max(F(5, 2) * n, 2 * v, 2 * n + v)
        if 35 * m + z < F(30 * n * n, max(n, v)) + 7 * v + F(n, 20):
            raise ArithmeticError("Invalid perturbed outer region")


def verify_cover(ray, polynomials, choices, depth_limit, dimension=3, outer_faces=((0, 1, 2),)):
    root = tuple(bernstein_grid(p, dimension) for p in polynomials)
    remaining = [(root, (F(0),) * dimension, (F(1),) * dimension, 0)]
    counts = [0] * len(choices)
    outside = max_depth = 0
    while remaining:
        grids, lower, upper, depth = remaining.pop()
        max_depth = max(depth, max_depth)
        if any(sum(lower[i] for i in face) >= 1 for face in outer_faces):
            outside += 1
            continue
        choice = next((i for i, group in enumerate(choices)
                       if all(grids[j].nonnegative for j in group)), None)
        if choice is not None:
            counts[choice] += 1
            continue
        if depth == depth_limit:
            raise ArithmeticError(f"Unverified box at ray {ray}: {lower} through {upper}")
        axis = max(range(dimension), key=lambda i: upper[i] - lower[i])
        midpoint = (lower[axis] + upper[axis]) / 2
        halves = list(zip(*(grid.halves(axis) for grid in grids), strict=True))
        remaining.append((halves[1], lower[:axis] + (midpoint,) + lower[axis + 1:], upper, depth + 1))
        remaining.append((halves[0], lower, upper[:axis] + (midpoint,) + upper[axis + 1:], depth + 1))
    return counts, outside, max_depth


def verify_ray(ray):
    verify_outer(ray)
    polynomials = objectives(*ray)
    choices = [(0,), (1, 2)] if len(polynomials) == 3 else [(0,)]
    counts, outside, depth = verify_cover(ray, polynomials, choices, 30)
    return counts[0], counts[1] if len(counts) > 1 else 0, outside, depth


if __name__ == "__main__":
    for ray in RAYS:
        plain, cuts, outside, depth = verify_ray(ray)
        print(f"Ray {ray}: {plain} base boxes, {cuts} two-cut boxes, "
              f"{outside} outer boxes, maximum depth {depth}.", flush=True)
    verify_outer_perturbation()
    print("Unbounded near-tail continuation constants verified.")

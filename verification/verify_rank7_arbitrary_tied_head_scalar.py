"""Check the three-variable scalar certificate for arbitrary tied-head tails."""

from fractions import Fraction
from itertools import product
from math import comb

from sympy import Poly, Rational, symbols

from verify_rank7_three_levels import bisect_controls


def axis_lines(degrees, axis):
    ranges = tuple(range(degree + 1) for degree in degrees)
    other_ranges = ranges[:axis] + ranges[axis + 1 :]
    for coordinate in product(*other_ranges):
        yield tuple(
            coordinate[:axis] + (index,) + coordinate[axis:]
            for index in ranges[axis]
        )


def initial_controls(polynomial):
    degrees = polynomial.degree_list()
    controls = {index: Fraction(value) for index, value in polynomial.terms()}
    for axis, degree in enumerate(degrees):
        weights = tuple(
            tuple(Fraction(comb(row, col), comb(degree, col)) for col in range(row + 1))
            for row in range(degree + 1)
        )
        transformed = {}
        for line in axis_lines(degrees, axis):
            values = tuple(controls.get(index, 0) for index in line)
            for index, row_weights in zip(line, weights):
                transformed[index] = sum(weight * value for weight, value in zip(row_weights, values))
        controls = transformed
    return degrees, controls


def positive_certificate(degrees, controls, max_depth):
    lines = tuple(tuple(axis_lines(degrees, axis)) for axis in range(len(degrees)))
    pending = [(controls, 0)]
    leaves = []
    while pending:
        patch, depth = pending.pop()
        lower_bound = min(patch.values())
        if lower_bound > 0:
            leaves.append(lower_bound)
            continue
        if depth == max_depth:
            raise ArithmeticError(f"Unproved patch at depth {depth}: {lower_bound}")
        left_patch, right_patch = {}, {}
        for line in lines[depth % len(degrees)]:
            left, right = bisect_controls(patch[index] for index in line)
            left_patch.update(zip(line, left))
            right_patch.update(zip(line, right))
        pending.append((left_patch, depth + 1))
        pending.append((right_patch, depth + 1))
    return len(leaves), min(leaves)


def main():
    z, v, u = symbols("z v u")
    scaled_z = Rational(9, 10) * z
    r = scaled_z**2
    t = r * v**2
    for separated in (True, False):
        w = scaled_z + (1 - scaled_z) * u if separated else scaled_z * u
        s = t * w**2
        expression = 3 * ((1 - r) * (1 - t) + 4 * s**2)**2 - 168 * s**2 * (1 - r - t - s)
        if separated:
            expression += 64 * (t * w * (w - scaled_z))**2
        degrees, controls = initial_controls(Poly(expression, z, v, u))
        count, bound = positive_certificate(degrees, controls, max_depth=24)
        label = "s >= r*t" if separated else "s <= r*t"
        print(f"{label}: {count} certified boxes, lower bound {bound}")


if __name__ == "__main__":
    main()

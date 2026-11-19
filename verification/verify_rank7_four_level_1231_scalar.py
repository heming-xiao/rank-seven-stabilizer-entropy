"""Check the scalar comparison for (1,r,r,s,s,s,w) with exact arithmetic."""

from functools import cache

from sympy import Poly, Rational, symbols

from verify_rank7_arbitrary_tied_head_scalar import initial_controls, positive_certificate
from verify_rank7_forward_coefficients import VERTICES


@cache
def matchings(vertices):
    if not vertices:
        return ((),)
    first, *remaining = vertices
    result = list(matchings(tuple(remaining)))
    for index, partner in enumerate(remaining):
        unpaired = tuple(remaining[:index] + remaining[index + 1 :])
        result.extend(((first, partner),) + suffix for suffix in matchings(unpaired))
    return tuple(result)


def verify_matching_charge():
    # Retain every ordered spectral gap, so the charge applies to the full spectrum.
    gaps = symbols("a0:7")
    weights = tuple(sum(gaps[index:]) for index in range(7))
    head, middle, third, a, b, c, d = weights
    maxima = {
        None: head * a + middle * b + third * c,
        (0, 1): head * middle + third * a + b * c,
        (0, 2): head * third + middle * a + b * c,
        (1, 2): middle * third + head * a + b * c,
    }
    counts = dict.fromkeys(maxima, 0)
    for matching in matchings(VERTICES):
        kind = next((edge for edge in matching if edge[1] <= 2), None)
        weight = sum(weights[i] * weights[j] for i, j in matching)
        core_edges = sum(j < 6 for _, j in matching)
        loss = maxima[kind] - weight - b * (c - d) * (3 - core_edges)
        if any(value < 0 for value in Poly(loss, *gaps).coeffs()):
            raise ArithmeticError(f"Unproved charge for matching {matching}")
        counts[kind] += 1
    if counts != {None: 154, (0, 1): 26, (0, 2): 26, (1, 2): 26}:
        raise ArithmeticError(f"Unexpected seven-label enumeration: {counts}")
    print(f"Full-spectrum conditional matching charge: {sum(counts.values())} comparisons")


def below_crossing(z, u, v, separated):
    # s <= r**2. Normalize by [r(1-r)]**2.
    r = z**2
    h = u / 2
    reference = r * (1 - r)
    root_floor_ratio = z + (1 - z) * v if separated else z * v
    scaled_gap = 1 - (1 - r) * h
    mix_base = scaled_gap + reference * h**2 * (18 * root_floor_ratio**2 - 2)
    mixed = Rational(3, 4) * mix_base**2 + scaled_gap**2 / 32
    gain = 168 * reference * h**2 * root_floor_ratio**2 * (
        1 - (2 + r) * h + reference * h**2 / 2
    )
    exterior = 48 * h**2 * r * (root_floor_ratio - z) ** 2 if separated else 0
    return mixed + exterior - gain


def above_crossing(z, u, v, separated):
    # s >= r**2. Normalize by r**2.
    root_r = Rational(3, 5) * z
    r = root_r**2
    root_tail_ratio = root_r + (Rational(71, 100) - root_r) * u
    root_floor_ratio = (
        root_tail_ratio + (1 - root_tail_ratio) * v
        if separated
        else root_tail_ratio * v
    )
    scaled_gap = (1 - r) * (1 - root_tail_ratio**2)
    mix_base = scaled_gap + r * root_tail_ratio**4 * (18 * root_floor_ratio**2 - 2)
    mixed = Rational(3, 4) * mix_base**2 + scaled_gap**2 / 32
    gain = 168 * r * root_tail_ratio**4 * root_floor_ratio**2 * (
        (1 - r) - (2 + r) * root_tail_ratio**2 + r * root_tail_ratio**4 / 2
    )
    exterior = (
        48 * r * root_tail_ratio**4 * (root_floor_ratio - root_tail_ratio) ** 2
        if separated
        else 0
    )
    return mixed + exterior - gain


def large_defect(r, u, v):
    # Normalize by [r(1-r)]**2 and use the rational lower bound on the positive part.
    h = u / 2
    t = r * (1 - r) * h**2
    scaled_gap = 1 - (1 - r) * h
    scaled_overlap = 1 - (2 + r) * h + t / 2
    mixed = Rational(11, 100) * scaled_gap + t * (3 * v - 2)
    return (
        Rational(1200, 11) * (mixed**2 - Rational(36, 625) * t**2)
        + Rational(11, 200) * scaled_gap**2
        - 168 * t * v * scaled_overlap
    )


def main():
    verify_matching_charge()
    z, u, v = symbols("z u v")
    for label, build in (("s <= r**2", below_crossing), ("s >= r**2", above_crossing)):
        for separated in (True, False):
            expression = build(z, u, v, separated)
            degrees, controls = initial_controls(Poly(expression, z, u, v))
            count, bound = positive_certificate(degrees, controls, max_depth=27)
            gap = "separated" if separated else "unseparated"
            print(f"Small defect, {label}, {gap}: {count} boxes, lower bound {bound}")
    degrees, controls = initial_controls(Poly(large_defect(z, u, v), z, u, v))
    count, bound = positive_certificate(degrees, controls, max_depth=21)
    print(f"Large defect: {count} boxes, lower bound {bound}")


if __name__ == "__main__":
    main()

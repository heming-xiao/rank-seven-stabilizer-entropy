"""Exact rank-seven comparisons for equal or nearby middle weights."""

from fractions import Fraction as F

from verify_rank7_four_equal_tails import (
    EXTERIOR_RATE, GEOMETRY, RESIDUAL, SQUARE, multiply, sum_polynomials,
    verify_cover,
)


def objectives(length_bound, shared_fraction, *, independent_middle_gap=False):
    one = {(): 1}
    scales = (length_bound, F(length_bound, 2), 1, F(1, 2), F(1, 3))
    h, k, p, r, s = ({(i,): scale} for i, scale in enumerate(scales))
    c = sum_polynomials((1, one), (1, s))
    b = sum_polynomials((1, c), (1, r))
    a = sum_polynomials((1, b), (1, p))
    if independent_middle_gap:
        q = {(5,): F(length_bound, 3)}
    else:
        q = multiply(b, {(5,): shared_fraction}) if shared_fraction else {}
    gamma = sum_polynomials((1, a), (1, q))
    beta = sum_polynomials((1, gamma), (1, k))
    alpha = sum_polynomials((1, beta), (1, h))

    delta = multiply(k, sum_polynomials((1, h), (1, k), (1, q)))
    anti = multiply(k, k, sum_polynomials(
        (1, multiply(k, k)), (F(1, 2), multiply(h, h)), (F(1, 2), multiply(q, q)),
    ))
    length = sum_polynomials((1, h), (2, k), (3, q))
    base = sum_polynomials(
        (2, one), ((1 - shared_fraction) / F(2), multiply(b, c, length)),
        (RESIDUAL, multiply(delta, p, p)), (-RESIDUAL, delta),
        (SQUARE / (GEOMETRY * EXTERIOR_RATE), multiply(delta, delta)),
        (1 / (GEOMETRY * EXTERIOR_RATE), anti),
    )

    outside = multiply(gamma, a, b)
    inside = multiply(c, beta)
    gap = sum_polynomials((1, inside), (-1, outside))
    denominator = sum_polynomials((1, inside), (1, outside))
    nested = sum_polynomials(
        (1, multiply(denominator, base)), (32 / EXTERIOR_RATE, multiply(alpha, gap, gap)),
    )
    return [base, gap, nested]


def verify_unequal_outer(length_bound, ratio):
    envelope = (SQUARE + F(1, 5)) / (GEOMETRY * EXTERIOR_RATE)
    debit = RESIDUAL**2 / (4 * envelope)
    if debit >= 2 + (1 - ratio) * length_bound / 2:
        raise ArithmeticError("Invalid unequal large-length bound")

    constant = 2 - (1 - ratio)**2 / (16 * RESIDUAL)
    root_term = F(3, 2) * (1 - ratio)
    # Check each lower quadratic at its unconstrained minimum.
    for intercept, slope in ((0, F(1, 3)), (F(12, 7), F(1, 7)), (4, 0)):
        linear = RESIDUAL - root_term * slope
        if constant + root_term * intercept <= linear**2 / (4 * envelope):
            raise ArithmeticError("Invalid unequal large-tail bound")


def main():
    envelope = (SQUARE + F(1, 3)) / (GEOMETRY * EXTERIOR_RATE)
    if RESIDUAL**2 >= 28 * envelope:
        raise ArithmeticError("Invalid large-length square bound")
    if not (envelope > RESIDUAL / 31 and F(105, 31) < 4 and F(195, 49) < 4 and F(31, 4) - 4 < 4):
        raise ArithmeticError("Invalid large-tail square bound")
    for length_bound, ratio in ((10, F(0)), (13, F(1, 5))):
        if ratio:
            verify_unequal_outer(length_bound, ratio)
        counts, outside, depth = verify_cover(
            (0, 1), objectives(length_bound, ratio), ((0,), (1, 2)), 42,
            dimension=5 + int(ratio > 0), outer_faces=((0, 1), (2, 3, 4)),
        )
        print(
            f"Middle gap / fifth probability <= {ratio}: {counts} comparison leaves, "
            f"{outside} outer leaves, depth {depth}.",
            flush=True,
        )


if __name__ == "__main__":
    main()


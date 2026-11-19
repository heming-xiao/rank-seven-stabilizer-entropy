"""Exact whole-spectrum comparison for the rank-seven three-equal-tail family."""

from fractions import Fraction as F

from verify_rank7_four_equal_tails import (
    BOUND, EXTERIOR_RATE, GEOMETRY, HIGHEST, RESIDUAL, SHARED,
    multiply, sum_polynomials, verify_cover, verify_outer,
)


RAYS = ((1, 0), (1, F(1, 2)), (1, 1), (1, 2), (1, 4), (0, 1))
TAIL_INCREMENT = F(9, 4)


def objectives(n, v, two_equal=False):
    one = {(): F(1)}
    h, k, q, p = ({(i,): scale} for i, scale in enumerate(
        (F(BOUND), F(BOUND, 2), F(BOUND, 3), F(1) if two_equal else TAIL_INCREMENT),
    ))
    floor_gap = {(4,): F(7, 2)} if two_equal else {}
    b = sum_polynomials((1, one), (1, floor_gap))
    a = sum_polynomials((1, b), (1, p))
    x = sum_polynomials((1, h), (1, k), (1, q))
    y = sum_polynomials((1, k), (1, q))
    alpha = sum_polynomials((1, a), (1, x))
    beta = sum_polynomials((1, a), (1, y))
    gamma = sum_polynomials((1, a), (1, q))
    g = multiply(h, q)
    delta = multiply(k, x)
    triangle = multiply(y, q)
    cubic = multiply(x, y, q)
    length = sum_polynomials((1, h), (2, k), (3, q))
    price = 1 - RESIDUAL
    completion = sum_polynomials(
        (1, cubic), (-price, multiply(g, sum_polynomials((1, y), (1, q)))),
        (-price, multiply(delta, q)),
    )
    f = multiply(a, cubic)
    anti = multiply(k, k, sum_polynomials(
        (1, multiply(k, k)), (F(1, 2), multiply(h, h)), (F(1, 2), multiply(q, q)),
    ))
    m = max(n, F(v) / 2)
    shared = max(n, v)
    z = max(F(5, 2) * n, 2 * v, 2 * n + v)
    base = sum_polynomials(
        (m, multiply(b, length)), (z, one), (SHARED * shared, multiply(g, g)),
        (HIGHEST * v, multiply(delta, delta)), (v / (GEOMETRY * EXTERIOR_RATE), anti),
        (-RESIDUAL * n, g), (-RESIDUAL * v, delta),
        (shared, multiply(length, p, p, p)), (shared, multiply(p, p, p, p)),
        (shared, multiply(completion, p)),
        (2 * RESIDUAL * shared, multiply(g, p, p)),
        (RESIDUAL * shared, multiply(delta, p, p)),
        (3 * shared, multiply(triangle, p, p)),
    )

    ab = multiply(a, b)
    exterior_debit = sum_polynomials((1, ab), (-1, one))
    top_denom = sum_polynomials((1, beta), (1, multiply(ab, gamma)))
    top_num = multiply(alpha, k, sum_polynomials((1, k), (-2, multiply(exterior_debit, gamma))))
    signed = sum_polynomials((1, f), (-F(1, 3), delta))
    trace_den = sum_polynomials((1, h), (2, multiply(a, x, y)))
    left_denom = multiply(sum_polynomials((1, gamma), (1, ab)), trace_den)
    left_num = multiply(alpha, sum_polynomials((1, q), (-2, multiply(a, floor_gap))), signed)
    right_denom = multiply(
        sum_polynomials((1, alpha), (1, multiply(ab, beta))), multiply(q, trace_den)
    )
    right_num = multiply(gamma, h, sum_polynomials((1, h), (-2, multiply(exterior_debit, beta))), signed)
    polynomials = [signed, sum_polynomials((9, multiply(x, y)), (-14, one))]
    choices = []

    def add(comparison, conditions=()):
        plain = len(polynomials)
        polynomials.append(comparison)
        choices.append((*conditions, plain))
        top = sum_polynomials(
            (1, multiply(top_denom, comparison)), (32 * v / EXTERIOR_RATE, top_num),
        )
        top_index = len(polynomials)
        polynomials.append(top)
        choices.append((*conditions, top_index))
        if n:
            for alternative, denominator in ((comparison, one), (top, top_denom)):
                left = sum_polynomials(
                    (1, multiply(alternative, left_denom)),
                    (48 * n / EXTERIOR_RATE, multiply(denominator, left_num)),
                )
                right = sum_polynomials(
                    (1, multiply(alternative, right_denom)),
                    (48 * n / EXTERIOR_RATE, multiply(denominator, right_num)),
                )
                index = len(polynomials)
                polynomials.extend((left, right))
                choices.append((*conditions, 0, index, index + 1))

    add(base)
    improvement = max(F(0), 2 * n + v - 3 * m)
    if improvement:
        add(sum_polynomials((1, base), (improvement, q)), (1,))
    return polynomials, choices


def verify_ray(ray):
    verify_outer(ray)
    if TAIL_INCREMENT**3 < F(BOUND, 3):
        raise ArithmeticError("Tail cutoff does not support the exterior comparison")
    polynomials, choices = objectives(*ray)
    return verify_cover(ray, polynomials, choices, 36, dimension=4)


if __name__ == "__main__":
    for ray in RAYS:
        counts, outside, depth = verify_ray(ray)
        print(f"Ray {ray}: {counts} comparison leaves, {outside} outer leaves, depth {depth}.", flush=True)

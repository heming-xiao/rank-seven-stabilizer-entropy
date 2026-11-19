"""Exact four-dimensional certificate with only the smallest three ratios bounded."""

from fractions import Fraction as F

from verify_rank7_four_equal_tails import (
    EXTERIOR_RATE, GEOMETRY, HIGHEST, RESIDUAL, SHARED,
    multiply, sum_polynomials, verify_cover, verify_outer_perturbation,
)
from verify_rank7_three_equal_tails import RAYS


U = F(101, 100)
OUTER = 35


def objectives(n, v, c_low, c_high, b_low=None, b_high=U):
    if b_low is None:
        b_low = c_low
    one = {(): F(1)}
    h, k, q, p = ({(i,): scale} for i, scale in enumerate(
        (F(OUTER), F(OUTER, 2), F(OUTER, 3), U),
    ))
    x = sum_polynomials((1, h), (1, k), (1, q))
    y = sum_polynomials((1, k), (1, q))
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
    anti = multiply(k, k, sum_polynomials(
        (1, multiply(k, k)), (F(1, 2), multiply(h, h)), (F(1, 2), multiply(q, q)),
    ))
    m = max(n, F(v) / 2)
    shared = max(n, v)
    z = max(F(5, 2) * n, 2 * v, 2 * n + v)
    tau = F(200, 11) * b_high * (c_high - 1)
    base = sum_polynomials(
        (m * c_low * b_low, length), (z - c_high * n * price * tau, one),
        (SHARED * shared, multiply(g, g)),
        (-(c_high * n * RESIDUAL + shared * F(15, 8) * tau / EXTERIOR_RATE), g),
        (HIGHEST * v, multiply(delta, delta)), (v / (GEOMETRY * EXTERIOR_RATE), anti),
        (-RESIDUAL * v, delta), (shared, multiply(length, p, p, p)),
        (shared, multiply(p, p, p, p)), (shared, multiply(completion, p)),
        (2 * RESIDUAL * shared, multiply(g, p, p)),
        (RESIDUAL * shared, multiply(delta, p, p)), (3 * shared, multiply(triangle, p, p)),
    )

    a_low = sum_polynomials((b_low, one), (1, p))
    a_high = sum_polynomials((b_high, one), (1, p))
    alpha_low = sum_polynomials((1, a_low), (1, x))
    gamma_low = sum_polynomials((1, a_low), (1, q))
    alpha_high = sum_polynomials((1, a_high), (1, x))
    beta_high = sum_polynomials((1, a_high), (1, y))
    gamma_high = sum_polynomials((1, a_high), (1, q))
    ratio = b_high / c_low
    theta = sum_polynomials((ratio, a_high), (-1, one))
    top_den = sum_polynomials((1, beta_high), (ratio, multiply(a_high, gamma_high)))
    top_num = multiply(alpha_low, k, sum_polynomials((c_low, k), (-2 * c_low, multiply(theta, gamma_high))))
    f = multiply(a_low, cubic)
    signed = sum_polynomials((1, f), (-F(1, 3), delta))
    trace_den = sum_polynomials((c_high, h), (2, multiply(a_low, x, y)))
    left_den = multiply(sum_polynomials((1, gamma_high), (b_high, a_high)), trace_den)
    left_num = multiply(alpha_low, sum_polynomials((c_low, q), (-2 * c_low * (b_high - 1), a_high)), signed)
    right_den = multiply(
        sum_polynomials((1, alpha_high), (ratio, multiply(a_high, beta_high))), q, trace_den,
    )
    right_num = multiply(
        gamma_low, h, sum_polynomials((c_low, h), (-2 * c_low, multiply(theta, beta_high))), signed,
    )
    polynomials = [signed, sum_polynomials((9, multiply(x, y)), (-14, one))]
    choices = []

    def add(comparison, conditions=()):
        plain = len(polynomials)
        polynomials.append(comparison)
        choices.append((*conditions, plain))
        top = sum_polynomials(
            (1, multiply(top_den, comparison)), (32 * v / EXTERIOR_RATE, top_num),
        )
        top_index = len(polynomials)
        polynomials.append(top)
        choices.append((*conditions, top_index))
        if n:
            for alternative, denominator in ((comparison, one), (top, top_den)):
                left = sum_polynomials(
                    (1, multiply(alternative, left_den)),
                    (48 * n / EXTERIOR_RATE, multiply(denominator, left_num)),
                )
                right = sum_polynomials(
                    (1, multiply(alternative, right_den)),
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


def verify_ray(ray, c_low, c_high):
    polynomials, choices = objectives(*ray, c_low, c_high)
    return verify_cover(ray, polynomials, choices, 38, dimension=4)


if __name__ == "__main__":
    verify_outer_perturbation()
    assert 1 <= U <= F(101, 100) and U**2 >= U
    endpoints = (F(1), (1 + U) / 2, U)
    for lower, upper in zip(endpoints, endpoints[1:]):
        for ray in RAYS:
            counts, outside, depth = verify_ray(ray, lower, upper)
            print(f"c in [{lower},{upper}], ray {ray}: "
                  f"{sum(counts)} accepted, {outside} outside, depth {depth}.", flush=True)


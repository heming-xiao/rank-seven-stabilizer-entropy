"""Check a uniform near-equal tail region by exact Bernstein bounds."""

from fractions import Fraction as F

from verify_rank7_four_equal_tails import (
    EXTERIOR_RATE, GEOMETRY, HIGHEST, RESIDUAL, SHARED,
    multiply, sum_polynomials, verify_cover, verify_outer_perturbation,
)


TAIL_RATIO = F(201, 200)
OUTER_GAP = 35
RAYS = ((1, 0), (1, F(1, 2)), (1, 1), (1, 2), (1, 4), (0, 1))


def objectives(n, v):
    """Construct conservative cost polynomials for all admitted tail values."""
    one = {(): F(1)}
    h, k, q = ({(i,): F(OUTER_GAP, i + 1)} for i in range(3))
    x = sum_polynomials((1, h), (1, k), (1, q))
    y = sum_polynomials((1, k), (1, q))
    alpha = sum_polynomials((1, one), (1, x))
    gamma = sum_polynomials((1, one), (1, q))
    g = multiply(h, q)
    delta = multiply(k, x)
    f = multiply(x, y, q)
    anti = multiply(k, k, sum_polynomials(
        (1, multiply(k, k)), (F(1, 2), multiply(h, h)), (F(1, 2), multiply(q, q)),
    ))
    m = max(n, F(v) / 2)
    z = max(F(5, 2) * n, 2 * v, 2 * n + v)
    shared = max(n, v)
    u = TAIL_RATIO
    tau = F(200, 11) * u * (u - 1)
    theta = u**2 - 1

    base = sum_polynomials(
        (m, h), (2 * m, k), (3 * m, q), (z - u * n * 30 * tau / EXTERIOR_RATE, one),
        (SHARED * shared, multiply(g, g)),
        (-(u * n * RESIDUAL + shared * F(15, 8) * tau / EXTERIOR_RATE), g),
        (HIGHEST * v, multiply(delta, delta)),
        (v / (GEOMETRY * EXTERIOR_RATE), anti), (-RESIDUAL * v, delta),
    )
    top_denom = sum_polynomials((2 * u**3, one), (u**2, k), (2 * u**2, q))
    top_gap = sum_polynomials((1, k), (-2 * theta * u, one), (-2 * theta, q))
    top_num = multiply(alpha, k, top_gap)
    signed = sum_polynomials((1, f), (-F(1, 3), delta))
    shared_denom = sum_polynomials((u, g), (2, f))
    left_denom = multiply(
        sum_polynomials((u + u**2, one), (1, q)),
        sum_polynomials((u, h), (2, multiply(x, y))),
    )
    left_num = multiply(alpha, sum_polynomials((1, q), (-2 * theta, one)), signed)
    right_denom = multiply(
        sum_polynomials((2 * u**3, one), (u**2, h), (2 * u**2, k), (2 * u**2, q)),
        shared_denom,
    )
    right_gap = sum_polynomials((1, h), (-2 * theta * u, one), (-2 * theta, k), (-2 * theta, q))
    right_num = multiply(gamma, h, right_gap, signed)
    full_head = sum_polynomials((9, multiply(x, y)), (-14, one))
    polynomials = [signed, full_head]
    choices = []

    def add(comparison, conditions=()):
        top = sum_polynomials(
            (1, multiply(top_denom, comparison)), (32 * v / EXTERIOR_RATE, top_num),
        )
        first = len(polynomials)
        polynomials.append(top)
        choices.append((*conditions, first))
        if n:
            polynomials.extend((
                sum_polynomials(
                    (1, multiply(top, left_denom)),
                    (48 * n / EXTERIOR_RATE, multiply(top_denom, left_num)),
                ),
                sum_polynomials(
                    (1, multiply(top, right_denom)),
                    (48 * n / EXTERIOR_RATE, multiply(top_denom, right_num)),
                ),
            ))
            choices.append((*conditions, 0, first + 1, first + 2))

    add(base)
    improvement = max(F(0), 2 * n + v - 3 * m)
    if improvement:
        add(sum_polynomials((1, base), (improvement, q)), (1,))
    return polynomials, choices


def verify_ray(ray):
    polynomials, choices = objectives(*ray)
    return verify_cover(ray, polynomials, choices, 33)


if __name__ == "__main__":
    verify_outer_perturbation()
    for ray in RAYS:
        counts, outside, depth = verify_ray(ray)
        print(f"Ray {ray}: {counts} comparison leaves, {outside} outer leaves, depth {depth}.", flush=True)

"""Exact row and arithmetic checks for paid shared nominal-width transport."""

from fractions import Fraction as F

from verify_rank7_low_head_tail_prices import CAPS, KNOWN_ROWS, REF, ROWS, WEDGES, verify_dual


def main():
    # This complement four-set covers exactly top wedge plus 123i, i=4,5,6.
    triple = [int({1, 2, 3} <= w) for w in WEDGES]
    index = KNOWN_ROWS.index(('four_set', (0, 4, 5, 6), 1))
    assert ROWS[index] == triple
    assert verify_dual([(index, '1')], ROWS, CAPS, triple) == sum(v*r for v, r in zip(triple, REF)) == 1
    # alpha*a-beta*gamma = gamma*h-alpha*q, an identity in a,h,k,q.
    for a in (1, 2):
        for h in (0, 1):
            for k in (0, 1):
                for q in (0, 1, 2):
                    gamma = a+q
                    beta = gamma+k
                    alpha = beta+h
                    assert alpha*a-beta*gamma == gamma*h-alpha*q
    rate = F(4242, 25)
    assert 24*max(2*F(3, 2), F(3, 2)+F(7, 4)) == 78
    assert (rate-102)*F(11, 5) > 144
    assert 2*(rate-36)*F(11, 5) > 48
    assert (rate-78)*F(33, 14) > 216 and (rate-78)*F(11, 6) > 168
    assert rate-36 > 48
    alpha, beta, gamma, b = F(649, 40), F(253, 40), F(11, 2), F(11, 10)
    h, k, q = alpha-beta, beta-gamma, gamma-b
    assert (h, k, q) == (F(99, 10), F(33, 40), F(22, 5))
    assert q >= max(b, F(11, 5))
    print("Verified the triple row and all constants for the nominal shared fourth-gap ray.")


if __name__ == "__main__":
    main()

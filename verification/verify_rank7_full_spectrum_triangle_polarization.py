"""Exact chamber check for the cone-free leading-triangle matching prices."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations

from verify_rank7_triangle_probe_tail_equalization import matchings


def raw_prices(gamma, a, b, c, d):
    return (c*(a-d)-gamma*(a-b), a*b-c*d-gamma*(a-c), a*b-c*d-gamma*(a-d))


def score_slack(matching, gaps, active, shift_index=None):
    values = tuple(sum(gaps[i:]) for i in range(7))
    alpha, beta, gamma, a, b, c, d = values
    raw = raw_prices(gamma, a, b, c, d)
    prices = tuple(value if i < active else 0 for i, value in enumerate(raw))
    score = sum(values[i]*values[j] for i, j in matching)
    score -= c*(b-d)*int((4,5) in matching) + d*(b-c)*int((4,6) in matching)
    score -= sum(prices[j-4] for i,j in matching if i < 3 and j >= 4)
    leading = next((e for e in matching if e[1] < 3), None)
    if leading:
        i,j = leading
        maximum = values[i]*values[j] + values[3-i-j]*a + c*d
    else:
        maximum = alpha*a + beta*b + gamma*c - prices[0] - prices[1]
    # In a chamber the first inactive row is nonpositive.
    first_inactive = -raw[active] if active < 3 else 0
    if shift_index is None:
        return maximum-score, first_inactive
    shift_candidates = (a*(gamma-b), c*(gamma-d))
    shift = shift_candidates[shift_index]
    cross_count = sum(i < 3 <= j for i,j in matching)
    full_count = 1 if leading else 3
    value = maximum - score - (full_count-cross_count)*shift
    shift_chamber = shift_candidates[1-shift_index]-shift
    return value, first_inactive, shift_chamber


def coefficients(matching, active, shift_index=None):
    units = [tuple(int(i == j) for j in range(7)) for i in range(7)]
    diagonal = [score_slack(matching, z, active, shift_index) for z in units]
    columns = list(diagonal)
    for i,j in combinations(range(7), 2):
        z = tuple(x+y for x,y in zip(units[i], units[j]))
        value = score_slack(matching, z, active, shift_index)
        columns.append(tuple(v-a-b for v,a,b in zip(value,diagonal[i],diagonal[j])))
    return columns


def verify_prices():
    counts = Counter()
    for matching in matchings(tuple(range(7))):
        for active in range(4):
            cols = coefficients(matching, active)
            if all(value >= 0 for value, _ in cols):
                counts["direct"] += 1
            elif all(value-row >= 0 for value,row in cols):
                counts["chamber"] += 1
            else:
                raise ArithmeticError(f"Missing nonnegative certificate for {matching}, {active}")
    if counts != {"direct":901, "chamber":27}:
        raise ArithmeticError(f"Unexpected certificate counts: {counts}")
    print("928 full-chamber comparisons (25984 exact quadratic coefficients); "
          "901 direct and 27 using one chamber row.")


def verify_completion_slack():
    counts = Counter()
    for matching in matchings(tuple(range(7))):
        for active in range(4):
            for shift_index in (0,1):
                columns = coefficients(matching, active, shift_index)
                for i,j in ((0,0),(0,1),(0,2),(0,3),(1,0)):
                    if all(value-i*raw-j*shift >= 0 for value,raw,shift in columns):
                        counts[i,j] += 1
                        break
                else:
                    raise ArithmeticError(f"Missing uniform shift certificate for {matching}")
    if counts != {(0,0):1331,(0,1):395,(0,2):89,(0,3):8,(1,0):33}:
        raise ArithmeticError(f"Unexpected shifted counts: {counts}")
    print("1856 further full-chamber comparisons (51968 coefficients) "
          "certify the additional positive completion price.")


def verify_open_region():
    alpha,beta,gamma,a,b,c,d = map(F, ("36","12","8","1.59","1.5","1.4","1"))
    B4,B5,B6 = tuple(max(value,0) for value in raw_prices(gamma,a,b,c,d))
    rho = min(b*(c-d),(gamma-c)*(a-b))
    delta = (beta-gamma)*(alpha-a)
    xi = 3*B4
    j = (beta-c)*(gamma-b)-c*(b-d)
    if not (gamma*d > a*b and alpha*c*d > beta*a*b and gamma*(a-b)<c*(a-d)
            and B4 == F(53,500) and B5 == B6 == 0 and xi < c*(b-d)
            and delta == F(3441,25) and rho == F(297,500) and j == F(341,5)
            and 800*xi*xi < delta*rho):
        raise ArithmeticError("Failed strict open-region or square-completion check")
    print(f"At the cone-exterior spectrum the fraction of the eta price spent is "
          f"{xi*xi/(delta*rho)} < 1/800.")


if __name__ == "__main__":
    verify_prices()
    verify_completion_slack()
    verify_open_region()

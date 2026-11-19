"""Verify two continuous-spectrum matching inequalities and the physical probe example."""
from fractions import Fraction as F
from functools import cache
from itertools import combinations


@cache
def matchings(vertices):
    if not vertices:
        return ((),)
    first, *tail = vertices
    result = list(matchings(tuple(tail)))
    for n, partner in enumerate(tail):
        rest = tuple(tail[:n] + tail[n+1:])
        result.extend(((first, partner),) + suffix for suffix in matchings(rest))
    return tuple(result)


def price_losses(matching, gaps):
    weights = tuple(sum(gaps[i:]) for i in range(7))
    alpha, beta, gamma, a, b, c, d = weights
    leading = next((edge for edge in matching if edge[1] <= 2), None)
    if leading:
        left, right = leading
        other = 3 - left - right
        maximum = weights[left]*weights[right] + weights[other]*a + b*c
    else:
        maximum = alpha*a + beta*b + gamma*c
    score = sum(weights[i]*weights[j] for i, j in matching)
    h = b*(c-d)
    margin = (gamma-c)*(a-b)
    e45, e46 = (4,5) in matching, (4,6) in matching
    ell = 3 - sum(j < 6 for _, j in matching)
    taxed_coefficient = ell + int(e45) - int(bool(leading))
    # For negative coefficient, rho <= margin. Otherwise rho >= 0 suffices.
    one_loss = maximum - score - h*ell + min(taxed_coefficient, 0)*margin
    rho45, rho46 = c*(b-d), d*(b-c)
    two_loss = maximum - score + rho45*(int(e45) - int(bool(leading))) + rho46*int(e46)
    cone = margin-rho45
    return one_loss, two_loss, cone


def quadratic_coefficients(matching):
    # The unit vectors and their pairwise sums recover every coefficient exactly.
    units = [tuple(int(j == i) for j in range(7)) for i in range(7)]
    diag = [price_losses(matching, x) for x in units]
    values = list(diag)
    for i, j in combinations(range(7), 2):
        x = tuple(l+r for l, r in zip(units[i], units[j]))
        values.append(tuple(a-b-c for a,b,c in zip(price_losses(matching, x), diag[i], diag[j])))
    return values


def verify_matching_prices():
    count, cone_count = 0, 0
    for matching in matchings(tuple(range(7))):
        values = quadratic_coefficients(matching)
        if any(one < 0 for one, _, _ in values):
            raise ArithmeticError(f"Single tax failed for {matching}")
        if any(two < 0 for _, two, _ in values):
            if any(two - cone < 0 for _, two, cone in values):
                raise ArithmeticError(f"Double tax failed for {matching}")
            cone_count += 1
        count += 1
    if count != 232:
        raise ArithmeticError("Wrong number of matchings")
    print(f"{count} single-tax and {count} double-tax inequalities verified in all 28 coefficients.")
    print(f"{cone_count} double-tax comparisons used the tail cone inequality.")


def verify_frame():
    # All coordinates are real. The four odd-label classes touched by the rotated leg
    # contribute half occupation. Eight odd labels per nonzero XOR direction.
    r_by_xor = {1: 1, 2: F(1,2), 8: F(1,2), 3: F(1,2), 9: F(1,2)}
    eta = sum(p*(1-p) for p in r_by_xor.values())
    weights = (44,20,15,F(3,2),F(5,4),F(11,10),1)
    alpha,beta,gamma,a,b,c,d = weights
    j = (beta-c)*(gamma-b) - c*(b-d)
    U = F(0)
    for wedge in combinations(range(7),4):
        if 2 not in wedge or wedge[0]^wedge[1]^wedge[2]^wedge[3]:
            continue
        for i,jj in combinations(range(3),2):
            if i in wedge and jj in wedge:
                k,l = sorted(set(wedge)-{i,jj})
                U -= F(1,2)*weights[k]*weights[l]
    improvement = 24*j*U + 12*j*j*eta
    if not (gamma*d > a*b and alpha*c*d > beta*a*b and gamma*(a-b) > c*(a-d)
            and eta == 1 and U == -F(2417,40) and j == F(1298,5) and improvement == 432234):
        raise ArithmeticError(f"Physical frame check failed: {eta}, {U}, {j}")
    print(f"Exact extra mixed payment on the specified four-qubit frame: {improvement}.")


if __name__ == "__main__":
    verify_matching_prices()
    verify_frame()

"""Exact strictly ordered example for the weighted highest-pair residual."""

from fractions import Fraction as F


def main():
    h, k, q, p, b, c, d = 15, F(1, 4), 6, F(1, 1000), F(191, 100), F(189, 100), 1
    a = b + p
    gamma, beta = a + q, a + q + k
    x, length, g = h + k + q, h + 2*k + 3*q, h*q
    delta = k*x
    r = k*k * (k*k + F(h*h + q*q, 2))
    tail = p*(a-c) + (b-d)*(c-d)
    discount = d*d-tail
    if not (a > b > c > d and beta*c*d < gamma*a*b):
        raise ArithmeticError("The example must be strictly ordered with no highest cut")
    if not (x*(d*d-tail) > b*c*d + p*q*(F(h, 2)+k+2*q+3*a-b-c-d)
            and 5*g > b*length):
        raise ArithmeticError("An earlier tail or small-shared criterion already applies")

    k_geom = F(5, 2)
    reserve = max(F(g*g, 24), F(q**4, 72))
    t_old = min(2*delta, delta+k_geom*d*d)
    old = (12*(2*t_old*delta-t_old*t_old)+r)/k_geom + reserve
    old -= (168*delta-24*t_old)*d*d - 168*k*b*c*d
    t = max(0, min(2*delta, delta+k_geom*(discount-p*q)))
    rho = 1-24*t/(168*delta)
    actual = (12*(2*t*delta-t*t)+r)/k_geom + reserve
    actual -= (168*delta-24*t)*discount - 168*k*b*c*d
    actual += 168*p*k*q*(rho*x+q+3*a-b-c-d-F(h, 2))
    if not old < 0 < actual:
        raise ArithmeticError("The two comparison margins must have opposite signs")
    print(f"Previous margin {old}, tail-weighted margin {actual}.")


if __name__ == "__main__":
    main()


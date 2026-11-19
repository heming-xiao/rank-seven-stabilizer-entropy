"""Exact example for the joint rank-seven counterexample-ratio criterion."""

from fractions import Fraction as F


def main():
    h, k, q, p, b, c = map(F, ("12.42", "0.0464", "1.88", "0.327", "1.181", "1.039"))
    a = b+p
    x, length, g = h+k+q,h+2*k+3*q,h*q
    gamma,beta = a+q,a+q+k
    delta = k*x
    discount = 1-p*(a-c)-(b-1)*(c-1)
    t = max(0,min(2*delta,delta+F(5,2)*(discount-p*q)))
    r = k*k*(k*k+(h*h+q*q)/2)
    h_tied = g-b*(h+3*q)-F(5,2)*b*b
    if not (h_tied<0 and beta*c<gamma*a*b and 5*g>b*length and q+2*k/c>b):
        raise ArithmeticError("Example does not have the claimed scope")
    high = (168*delta-24*t)*discount-168*k*b*c
    high -= 168*p*k*q*((1-24*t/(168*delta))*x+q+3*a-b-c-1-h/2)
    high -= (12*(2*t*delta-t*t)+r)/F(5,2)+max(g*g/24,q**4/72)
    reserve = (g*g/24)*b*length/(10*g)
    if not (0<high<F(1,10) and reserve>2):
        raise ArithmeticError("Exact residual and shared reserve did not match")
    print("Exact residual in (0,1/10); the shared-reserve threshold exceeds 2.")


if __name__ == "__main__":
    main()


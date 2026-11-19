"""Check the rational slope bounds and six-ray transfer example."""

from fractions import Fraction as F


RATE = F(4242, 25)
MATCHING_PRICE = F(200, 11)
GEOMETRY = F(5, 2)
RAYS = ((1, 0), (1, F(1, 2)), (1, 1), (1, 2), (1, 4), (0, 1))


def score(gaps, tail_gap, n, v, shared_weight=F(3, 4), highest_weight=F(7, 4)):
    h, k, q, p, c = gaps
    b = c + tail_gap
    a = b + p
    x, y, length = h + k + q, k + q, h + 2*k + 3*q
    g, delta, j = h*q, k*x, y*q
    h_tail = max(b*(c-1) - p*(a+q-c), 0)
    shared = max(g - MATCHING_PRICE*h_tail, 0)
    s, t = shared_weight*shared, highest_weight*delta
    lam, mu = 24*s/RATE, 24*t/RATE
    completion = x*y*q-lam*(y+q)-mu*q
    assert completion >= 0
    peak, price = max(n, v), max(n, F(v)/2)
    floor = max(F(5, 2)*n, 2*v, 2*n+v)
    geometry = max(2*n+v-3*price, 0)
    shared_payment = (g*g+12*s*(2*shared-s)+(1+tail_gap**2)*g*g/(h*h+3*q*q))/(12*RATE)
    highest_anti = k*k*(k*k+(h*h+q*q)/2)
    highest_payment = (highest_anti+12*t*(2*delta-t)+(1+tail_gap**2)*k*k/2)/(GEOMETRY*RATE)
    head = (length*p*(a-c)*(a-1)+p**4+2*(g-lam)*p*p
            +(delta-mu)*p*(a-c)+3*j*p*p+completion*p)
    tail = (delta-mu)*(b-1)*(c-1)*max(v, F(n)/2)
    return (b*c*length*price+floor+(head+shared_payment)*peak+tail
            +min(q, b*completion)*geometry+highest_payment*v-c*(g-lam)*n-(delta-mu)*v)


def verify():
    assert MATCHING_PRICE/RATE*(F(56, 75)+F(720, 91)) < F(15, 16)
    assert MATCHING_PRICE/RATE*(F(22, 3)+F(72, 65)) < F(15, 16)
    assert 1920 < 44**2 and 1920*F(9, 5)*F(1, 5) > 26**2
    gaps = tuple(map(F, ("9.41", "1.23", "2.8", ".01", "1.18")))
    h, k, q, p, c = gaps
    length = h+2*k+3*q
    assert h*q < 160*c*(2-c) and length > F(7, 5)*(2*c-1)
    slope = c*length-MATCHING_PRICE/RATE*max(c-1-p, 0)*(4*h*q+36*c)
    assert slope > 21
    scores = [score(gaps, F(0), n, v)/max(n, F(v)/2) for n, v in RAYS]
    assert -F(6, 5) < min(scores) < -1
    target = F(7, 50)
    assert min(scores) + slope*target > 0
    for (n, v), baseline in zip(RAYS, scores, strict=True):
        value = score(gaps, target, n, v)
        assert value >= (baseline+slope*target)*max(n, F(v)/2)
    print("Verified the monotone slope constants and the six-ray transfer exactly.")


def verify_two_gap_transfer():
    h, k, q, c = map(F, ("9.41", "1.23", "2.8", "1.18"))
    p, tail_gap = F(1, 100), F(7, 50)
    x, y, length = h+k+q, k+q, h+2*k+3*q
    g, delta, j = h*q, k*x, y*q
    baseline = min(score((h, k, q, F(0), c), F(0), n, v)/max(n, F(v)/2)
                   for n, v in RAYS)
    slope = c*length-MATCHING_PRICE*(c-1)*(4*g+36*c)/RATE
    completion = x*y*q-36*g*(y+q)/RATE-42*delta*q/RATE
    uplift = (p*completion+p**4+length*p**3
              +(1-36/RATE)*g*p*(2*p+c-1)
              +(1-42/RATE)*delta*p*p+j*p*(3*p+2*c-1))
    assert -4 < baseline < -F(39, 10)
    assert baseline+slope*tail_gap < 0 and baseline+uplift < 0
    assert baseline+slope*tail_gap+uplift > F(6, 25)


if __name__ == "__main__":
    verify()
    verify_two_gap_transfer()


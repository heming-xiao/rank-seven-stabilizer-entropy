# Rank-seven optimality when the smallest two ratios are within one percent

November 18, 2026. For any sorted positive Schmidt probabilities
\((\alpha,\beta,\gamma,a,b,c,d)\) satisfying
\[
                              c\le(101/100)d ,
\]
the sorted computational representative minimizes order-two nonlocal
stabilizer Rényi entropy over arbitrary complex local unitaries on
every qubit bipartition. The first five entries have arbitrary ratios.
This includes the entire two-equal-smallest family, and fully distinct
spectra with unbounded fifth-to-seventh ratio. The single-frame proof
retains at least \(1/101\) of the actual Pauli and compression defects,
so each positive spectrum in the stated closed region also has an
unrestricted relative open neighborhood of optimality.

Use all definitions and physical estimates from the
[one-percent three-tail proof](rank7_near_three_tails.md). Normalize
\(d=1\) and set \(u=101/100\). That theorem covers \(b\le u\).
For \(b\ge u\), the next two analytic comparisons and a finite
four-variable certificate give the result.

## Two unbounded regions

On \(E>0\), the pure [low-head inequality](rank7_low_head_tail_prices.md)
forces \(q+2k/c>b\). Consequently \(L=h+2k+3q>b\).
Also \(p=a-b\ge u\) already gives \(E\le0\) at any \(b\), since
\(D_4\ge p^2XY\), \(XY\ge g+\Delta\), and \(p^2\ge c,1\).
It suffices on \(E>0\) to treat \(p<u\).

To cover arbitrarily large \(b\), keep just the shared and individual
squares and the singleton coupon \(bcLM\); the two compression
cuts and \(Z_N\) can be discarded. Let
\[
 s_g=\frac{49}{48b_*},\qquad
 s_\Delta=\frac{45/4+1/5}{(5/2)b_*},\quad
 r=1-\rho,\quad\rho=30/b_*,\quad D=\frac{15}{8b_*},\quad
 T=\frac{200}{11}(u-1).
\]
Here \(b_*=(101/100)168\) and \(R\ge\Delta^2/5\).
Completing the two squares in the base (3) of the three-tail
proof bounds the total debit by
\[
 W(b)=\frac{(ur n+D T b P)^2}{4s_gP}
                 +u\rho T b n+\frac{r^2 v}{4s_\Delta}. \tag{1}
\]
If \(P=0\), the exterior comparisons already give \(E\le0\).
For \(b\ge10\), division by \(b^2\) gives
\[
 W(b)/b^2\le
 \frac{(ur n/10+DTP)^2}{4s_gP}
           +u\rho T n/10+\frac{r^2v}{400s_\Delta}.
\]
The verifier checks that this is at most \(M\) on each of the six
geometric rays. This ray test is valid despite the squared quotient:
on each geometric sector \(P\) is linear and positive and
\((x,P)\mapsto x^2/P\) is convex and positively homogeneous.
Thus the upper bound is subadditive on combinations of its boundary
rays, while \(M\) is linear there. We have \(bcLM\ge b^2M\) on
\(E>0\), proving the large-\(b\) claim.

For each compact strip \(\ell_b\le b\le z_b\) specified below,
\(W(z_b)\) bounds the debit. For \(L\ge35\) the six ray tests
in the verifier give
\[
                   35\ell_b M+Z_N\ge W(z_b).
\]
The same perspective convexity justifies interpolation of this check.
Now retain \(Z_N\) together with \(bcLM\). This finishes the entire
\(L\ge35\) region independently of compression.

## Compact strips and their four-variable comparison

Partition the remaining \(b\) interval at the rational endpoints
\[
 1.01,\ 1.02,\ 1.04,\ 1.07,\ 1.1,\ 1.2,\ 1.4,\ 1.7,\
 2.1,\ 2.8,\ 4,\ 6,\ 10 .
\]
Within each strip use the same two intervals
\([\ell,z]=[1,201/200],[201/200,101/100]\) for \(c\).
In the scalar comparison (3) of the three-tail proof, use
\(\tau=(200/11)z_b(z-1)\) and replace \(\ell^2 LM\) by
\(\ell_b\ell LM\). Every other term is unchanged, since the
retained wedge prices use the actual fourth gap \(p=a-b\);
all three weighted probe deficits still satisfy (1) of that proof.

For (4) of that proof and for the shared trace multiplier take
\[
 a_-=\ell_b+p,\quad a_+=z_b+p,\quad
 A=(z_b/\ell)a_+,\quad\theta=A-1 .
\]
The left shared candidate now uses
\(q(q-2a_+(z_b-1))/[2(\gamma_++z_b a_+)]\) times
\(\ell\alpha_-\). The top and right candidates retain the same
form with the displayed \(A,\theta\). These substitutions follow
from \(a_-\le a\le a_+\), \(ab/c\le A\) and \(b-1\le z_b-1\).
The shared trace numerator \(a_- XYq-\Delta/3\) and denominator
\(zg+2a_- XYq\) retain the required monotonicities.
This supplies a uniform lower comparison for every point of each
strip.

At \(L<35,\ p<u\), the same unit four-cube rescaling as before
suffices. The [standard-library verifier](../verification/verify_rank7_near_two_tails.py)
calls the [shared polynomial builder](../verification/verify_rank7_near_three_tails.py)
with the separate bounds for \(b,c\). After clearing denominators it
checks the base, optional highest cut, both conditional shared
alternatives, and optional geometric improvement on the same dyadic
box. For each interval pair the six rays use
\((n,v)=(1,0),(1,1/2),(1,1),(1,2),(1,4),(0,1)\).

| \(b\) interval | Comparison leaves, both \(c\) bins | Outer leaves, both bins | Max. depth |
|---|---:|---:|---:|
| 1.01–1.02 | 646 | 74 | 18 |
| 1.02–1.04 | 651 | 74 | 18 |
| 1.04–1.07 | 632 | 74 | 15 |
| 1.07–1.1 | 614 | 74 | 15 |
| 1.1–1.2 | 663 | 74 | 14 |
| 1.2–1.4 | 569 | 70 | 17 |
| 1.4–1.7 | 353 | 62 | 13 |
| 1.7–2.1 | 225 | 50 | 10 |
| 2.1–2.8 | 152 | 32 | 10 |
| 2.8–4 | 90 | 22 | 6 |
| 4–6 | 56 | 12 | 6 |
| 6–10 | 24 | 4 | 2 |

The 144 trees yield 4,675 comparison leaves and 622 outer leaves,
with maximum depth 18. The earlier \(b\le u\) branch uses 658
comparison and 74 outer leaves. All interval endpoints are included.
The resulting bound on \(E>0\) pays \(b_*E\) out of the true
Pauli-plus-compression sum. On \(E\le0\) the full actual defects
remain. This proves the strict factor and the claimed global
comparison by the paired reduction and stabilizer padding.
[Paired transfer and open neighborhoods](rank7_open_interior_neighborhood.md)


# Rank-seven optimality above a three-to-one fifth-to-last ratio

November 18, 2026. On any qubit bipartition, with arbitrary complex
local unitaries, the sorted computational representative minimizes
order-two nonlocal stabilizer Rényi entropy for every ordered positive
rank-seven spectrum proportional to \((\alpha,\beta,\gamma,a,b,c,d)\)
with
\[
                              b\ge 3d. \tag{1}
\]
There is no restriction on the four larger entries or on \(c\).
At every such spectrum the proof retains a positive paired-defect
margin, including when \(b=3d\). The rank-seven equality classification
and the unrestricted local spectral neighborhoods therefore apply.
[Equality and neighborhood transfer](rank7_all_tie_equalities.md)

Normalize \(d=1\) by homogeneity. Write \(h=\alpha-\beta,\ k=\beta-\gamma,\ 
q=\gamma-a,\ X=h+k+q,\ Y=k+q,\ L=h+2k+3q,\ g=hq,\ \Delta=kX\).
Put \(A=(101/100)168,\ K=5/2,\ \rho=1-24/A,\ J=(12+1/5)/(KA)\).
The statistics \(n=(L_{01}+L_{02}-4)_+\) and \(v=(L_{01}-2)_+\)
are the positive trace excesses of the two leading edge families.
Write \(E\) for the normalized linear exterior gain,
\(U_1\) for the highest-pair weighted gain and \(D\) for the sum
of the actual defects in paired purity units. Its comparison target is
\(168E\). The tied-middle theorem covers \(k=0\).
[Definitions and paired reduction](rank7_two_probe_separation_and_tail_region.md)

## Canceling the shared trace when the tied-middle gain is nonpositive

Let \(H=g-b(h+3q)-(5/2)b^2\) and assume \(H\le0\).
Choose the highest mixed shift \(t=\Delta\), zero other shifts, and
set \(\mu=24\Delta/A\). Two upper bounds hold on the same frame:
\[
\begin{aligned}
 E-\mu U_1&\le cgn+\rho\Delta v-bcL\max(n,v/2),\\
 E-\mu U_1&\le cHn+\rho\Delta v-kbc\,v . \tag{2}
\end{aligned}
\]
The first is the signed exterior expansion with its weighted
singleton loss. Its completion coefficient is \(q(XY-\mu)\ge0\),
since \(\Delta\le XY\). For the second compare to the spectrum with
its first two entries lowered by \(k\). The actual-frame split gives
\(E\le E_0+\Delta U_1-kbc\,v\). At that spectrum \(E_0\le cHn\):
on positive shared excess use the weighted tied-middle bound and on
nonpositive excess use \(E_0\le0\). The five-tail prefix bound gives
\(U_1\le v\). These prove (2) for either sign of the raw excesses.
[Signed singleton loss](rank7_low_head_tail_prices.md) ·
[Weighted split](rank7_weighted_split_residual.md) ·
[Tied-middle bound](rank7_equal_middle.md)

Put \(\theta=1-g/[b(h+3q)+(5/2)b^2]\in[0,1]\).
Take the first bound of (2) with weight \(\theta\) and the
second with weight \(1-\theta\). Their terms on \(n\) cancel after
using \(\max(n,v/2)\ge v/2\). On **every** ordered spectrum with
\(H\le0\) this proves the single-observable exterior bound
\[
 E-\mu U_1\le
  [\rho\Delta-kbc-\tfrac12\theta bc(h+3q)]v . \tag{3}
\]
Both inputs are exterior estimates. The actual highest mixed square
still pays \(24\Delta U_1+12\Delta^2\kappa_1\). Independent
anticommuting slots pay \(R\kappa_1+g^2\kappa\), where
\(R=k^2[k^2+(h^2+q^2)/2]\ge\Delta^2/5\).
Using \(\kappa_1\ge v/K,\ \kappa\ge v/12\) gives \(D\ge AE\)
as soon as
\[
 \rho V-Jb^2V^2\ \le\
 w+\frac{x}{2}\left(1-\frac{G}{x+5/2}\right)
        +\frac{b^2G^2}{12A},\quad
 x=\frac{h+3q}{b},\quad G=\frac{g}{b^2},\quad
 w=\frac{k}{b},\quad V=\frac{\Delta}{b^2}. \tag{4}
\]
Indeed divide the payment per \(v\) by \(Ab^2\) and lower bound
\(c\) by one on the first two nonnegative terms on the right.
For \(v=0\) the comparison before division suffices directly.
[Highest mixed and independent anticommuting slots](rank7_compact_remaining_spectra.md)

Here \(G\le x^2/12\) and \(V\le w(w+x)\). For \(b\ge3\) the
left side of (4) is at most \(\rho^2/(36J)<18/25\).
If \(G\ge13\) the final term alone exceeds \(18/25\). Otherwise:

* For \(2\le x\le25/2\) the middle term is at least
  \(f(x)=x/2-x^3/[24(x+5/2)]\). This function is concave, since
  the second derivative of \(x^3/(x+r)\) is \(2-2r^3/(x+r)^3\)
  for \(r=5/2\). Both endpoints \(25/27,475/576\) exceed \(18/25\).
* For \(x\ge25/2\), use \(G\le13\). The middle term is at least
  \((25/4)(1-13/15)=5/6\).
* For \(x\le2\), \(G/(x+5/2)\le2/27\), so the first two terms
  pay \(m=w+(25/54)x\). If \(m\ge18/25\) we are done.
  Otherwise \(w(w+x)\le(729/725)m^2\), by completing the square
  in \(w\) for fixed \(m\). Thus \(\rho V\le(729/725)(18/25)m<m\)
  when \(m>0\); at \(m=0\) both sides vanish.

This proves the full \(H\le0\) branch without using any compression
threshold, common-frame matching correction, or shared mixed shift.

## The positive tied-middle branch

For \(H>0\), \(G>x+5/2\ge2\sqrt{3G}+5/2\) implies
\(G>17/2+\sqrt{66}>299/18\), so \(g>299/2\) when \(b\ge3\).
The [weighted transfer](rank7_weighted_split_residual.md), taken
at its admissible shift \(t=\Delta\), suffices with strict margin if
\[
 144\Delta-\frac{122}{25}\Delta^2
             <168kbc+g^2/24. \tag{5}
\]
Here its weighted residual multiplier \(1-(a-b)(a-c)-(b-1)(c-1)\)
is at most one, the completion debit is nonnegative, and the
highest anticommuting coefficient satisfies \(R\ge\Delta^2/5\).
The transfer has already reserved the shared half of the
anticommuting payment in its positive branch.

The left side of (5) is at most \(64800/61\).
If \(g\ge160\), \(g^2/24\) exceeds that value. If \(k\ge13/50\),
then \(168kbc+g^2/24>504(13/50)+(299/2)^2/24>64800/61\).
In the remaining case \(X=k+h+q\le k+h+3q<k+g/b-5b/2<47\).
Thus \(168kbc\ge504\Delta/47\), and the maximum of
\((144-504/47)\Delta-(122/25)\Delta^2\) is strictly below
\((299/2)^2/24\). This proves (5). Its strict margin at each
spectrum, or the factor \(A/168\) in the other branch, yields the
paired conclusions stated in (1). The
[exact checker](../verification/verify_rank7_large_fifth_probability.py)
verifies the rational inequalities, endpoint values and polynomial
identities used in both branches.

## A head-gap region below the fifth-probability threshold

With arbitrary \(d>0\) and all four tails unrestricted the same global
optimality and equality conclusions hold when
\[
 \boxed{\quad \big(q\le b/2\ \text{or}\ h\le3b/2\big),\qquad
                  bc(h+4k+3q)\ge22d^3.\quad} \tag{6}
\]
Return to \(d=1\). The first condition gives \(g\le b(h+3q)/2\),
so \(H<0\) and \(\theta\ge1/2\). Retain the pure-floor deficit in
the first bound of (2). Its contribution is \(7-N\ge2v\), supplementing
the separate singleton price from that bound. The same convex weights
as before now yield
\[
 E-\mu U_1\le[\rho\Delta-kbc-\theta(bc(h+3q)/2+2)]v .
\]
The two negative prices sum in magnitude to at least
\(1+bc(h+4k+3q)/4\ge13/2\). But
\(\rho\Delta-J\Delta^2\le\rho^2/(4J)<13/2\).
This pays \(AE\) before using the shared anticommuting or either
compression term. [Pure-floor trace price](rank7_uniform_cut_packing.md)

More precisely in the general \(H<0,\ g>0\) branch, put
\(D_*=\rho\Delta-J\Delta^2-g^2/(12A)\).
If a paired frame violates the target \(D\ge AE\), then \(v>0\)
and both inequalities in (2), with their respective floor terms,
impose
\[
 \frac{bcL/2+2-D_*}{cg}<\frac{n}{v}
                     <\frac{D_*-kbc}{-cH}. \tag{7}
\]
This is an exclusion for the physical payment at the strengthened
factor \(A/168\). Empty intervals therefore prove optimality with
the \(1/101\) margin. The right endpoint uses the negative
tied-middle gain on the actual frame.

For a strictly ordered example inside (6), take
\((h,k,q,p,b,c,d)=(8,3/2,1/2,1/40,7/5,11/10,1)\).
Both true basic cuts have zero width, as \(\beta c<\gamma ab\)
and \(\gamma<ab\). The older small-shared inequality fails, and the
optimized [weighted residual](rank7_weighted_split_residual.md) exceeds
\(511\), also failing the preceding excess-ratio exclusion. At this
spectrum the relaxation with the 98 capacity rows and all 21 physical
pair caps admits the following array, indexed by complementary triples:

| Weight | Triples |
|---|---|
| \(1/6\) | \(035,045,134,135,145\) |
| \(2/6\) | \(015,025,026,124,125,136,234,235,236,246,356\) |
| \(3/6\) | \(034\) |
| \(4/6\) | \(016,456\) |

Set every other weight to zero. Its normalized exterior gain is
\(752983/7680000>0\). This witnesses the insufficiency of the
linear exterior comparison using those 119 constraints. Condition (6)
settles the physical purity comparison on the entire region.

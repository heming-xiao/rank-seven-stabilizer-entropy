# Independent review of rank-seven fourth-gap seed transfer

November 18, 2026. The independent Sol reviewer inspected the
lower-fifth source and the new seed transfer proofs. The interval
execution receipts are in the round log. The reviewer used source
inspection and independent symbolic bounds.

## Compression-free lower branch

Undo the lower checker's normalization by multiplying its weighted
margin by \(b^2\) with \(d=1\). The checked margin is
\[
\frac{12w(2-w)\Delta^2+R}{K}+
\max(g^2/24,q^4/72)+168kb-(168-24w)\Delta>0.
\]
At any \(p\ge0\), the full weighted test has \(D_0(p)\le1\),
\(c\ge1\), and a nonpositive completion debit because
\(\rho=1-w/7\ge3/4\) and \(3a\ge b+c+1\). Its compression
payment can be dropped, so the checked margin suffices along the full
ray.

## Mixed lower branch

Both exterior alternatives prepay the explicit upper allowance
\(\gamma_0h(b-c)w_{1234}/2\). The shifts and splitting parameter
are common across the two \(c\) endpoints and each adjacent ray
pair. The highest cut is assigned zero and the shared trace price is
\(n[1-\min(1/2,n/(3v))]\le n\le e\) in the positive-excess sector.
These facts establish the input comparison in the mixed-ray lemma.

The bound on the six-mode correction can be frozen at \(b(c-1)\)
throughout the ray. The lower quadratic norm stays valid for
\(\Psi\ge(h^2+q^2)/6\) irrespective of \(p\). The chosen \(s\)
is at most \(3/2\) times the effective lower shared gain divided by
its completion factor, so the shared quadratic stays nonnegative.
For the two simultaneous shifts the Gram cross coefficient
\(s\Delta+tg-st\) is nonnegative by checking each corner of
\(s/g\in[0,3/2],t/\Delta\in[0,7/4]\).

## Upper weighted branch

For the only exceptional longer-shift case \(48q<r c/b\) with
\(r=343/10\), the reviewer recovered
\(c/b>320/343,\ b<343/240,\ c>1280/1029\).
A positive highest seed width requires
\(k>(b+q)(b^2/c-1)\ge2/3\), so the seed tail discount is less
than \(2836/3087\). At \(\Delta\ge(1800/61)D_0(0)\) the
compression-free criterion at \(t=\Delta\) pays all the loss
because \((122/25)\Delta^2\ge144\Delta D_0(0)\).
Otherwise \(X<(2700/61)(2836/3087)\). After using \(48qX\),
the width debit is bounded by \((r-32)X+rb\), and the remaining
exterior terms pay at least \(112/3+112\). The stated exact
rational gap is positive. If the seed width vanishes, its variation
cannot create a loss.

[Transfer proof](../rank7_seed_branch_transfer.md) ·
[Mixed-cut proof](../rank7_mixed_cut_full_fourth_ray.md) ·
[Lower checker](../../verification/verify_rank7_tied_fourth_lower_fifth.cpp).


## Lower verifier coverage and provenance

For an unresolved spectrum with \(d=1\), \(b\le4/3\), the
bottom-pair and small-third-gap theorems give \(b\ge c>101/100\)
and \(x=q/b>1/2\). The small-shared and small-middle tests give
\(5zx>z+2y+3x\) and \(96y>c\). These imply \(z>3/5\),
\(y>1/96\), and the positive-denominator contractor for \(z\).
The low-head exclusion gives \(q+2k/c>b\), so \(x+2y>1\).
The earlier compact-domain inequalities supply the other strict cap
values. Positivity of the actual shared gaps implies positivity of each
seed gap since each decreases by \(p(b-1)\). The contractor replaces each
key coefficient by the corresponding outward endpoint. The integer
cross products for mixing are equivalent to strict intersection of the
two positivity half-intervals. The trace values match all seven listed
rays, including the monotone trace lower bound in the last sector.

The reviewer confirmed that both frozen source SHA-256 hashes match the
lower proof note. This was an independent source-and-proof review. The
logged interval traversals were run separately.

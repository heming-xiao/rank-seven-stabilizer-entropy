# Rank-seven optimality under two leading spectral-ratio conditions

Let \((\alpha,\beta,\gamma,a,b,c,d)\) be arbitrary ordered positive
Schmidt probabilities, \(p=a-b\), \(h=\alpha-\beta\), \(k=\beta-\gamma\),
and \(q=\gamma-a\). The sorted computational representative is globally
optimal over arbitrary complex local unitaries on every qubit cut if
\[
         dh\le(b-d)(\beta-p),\qquad dk\le(b-d)(\gamma-p).             \tag{1}
\]
When \(a=b\), these are exactly \(\alpha d\le\beta b\) and
\(\beta d\le\gamma b\), which make both shared and highest
**nominal** compression widths vanish. The shared width also
vanishes through a separate crossing when \(\gamma d\le ab\).
This proof establishes the stated ratio subfamily,
including \(H>0\), needs no compression payment. The proof gives
a per-spectrum strict paired-defect margin and thus the local
Clifford equality and open-neighborhood conclusions.
[Nominal widths](rank7_full_nominal_widths.md) ·
[Equality transfer](rank7_all_tie_equalities.md)

## A simultaneous split and mixed payment

Normalize \(d=1\). Set \(X=h+k+q,\ L=h+2k+3q,\ g=hq,\ \Delta=kX,\)
\(H=g-b(h+3q)-5b^2/2,\ A=(101/100)168,\ K=5/2\).
Previous comparisons cover any potentially violating frame with
either \(n=\nu\le0\) or \(v=L_{01}-2\le0\); use \(n,v>0\) below.
Write \(P=\max(n,v)\), \(M=\max(n,v/2)\), \(U,U_1\) for the
two weighted probe differences, and \(E\) for the normalized linear
exterior gain. Choose \(s,t\ge0,\ \lambda=24s/A,\ \mu=24t/A\)
as specified below. They obey \(s\le3g/2,\ t=5\Delta/4\) and
\(\lambda\le g/2,\ \mu\le\Delta/2\).

Two exterior estimates with the very same shifts are
\[
\begin{aligned}
 E-\lambda U-\mu U_1
      &\le c(g-\lambda)n+(\Delta-\mu)v-bcL M-2v ,\\
 E-\lambda U-\mu U_1
      &\le c(H-\lambda)n+(\Delta-\mu)v-kbc\,v .                     \tag{2}
\end{aligned}
\]
The first is the signed head expansion with its weighted singleton
and pure-floor deficits, \(7-N\ge2v\). Its completion coefficient
is nonnegative for these prices and all auxiliary deficits may be
dropped. [Weighted singleton](rank7_low_head_tail_prices.md) ·
[Pure-floor bound](rank7_uniform_cut_packing.md)

For the second, lower the two highest probabilities by \(k\) on
the fixed frame and call its gain \(E_0\). With the nonnegative
completion deficit \(D_A\), one has
\(B=cn-U=B_0+kD_A,\ U_1\le v-qD_A\). The tied-middle bound and
the split estimate give
\[
 E_0\le cHn-gB_0/2,\qquad
 E-E_0\le\Delta U_1-kbc\,v-kq(q+3a-b-c-1)D_A .
\]
Subtract both probe prices. The coefficient of \(B\) is
\(-g/2+\lambda\le0\). The coefficient of \(D_A\) is at most
\(kg/2-q(\Delta-\mu)\le0\), since \(X\ge h\).
This establishes (2), for both signs of \(H\).
[Tied-middle transport](rank7_harmonic_tail_transport.md) ·
[Highest split](rank7_highest_pair_split_loss.md)

## Three scalar variables for all four tails

Use \(z=h/b,\ y=k/b,\ x=q/b,\ G=zx,\ D=y(z+y+x)\), and
\[
 \begin{gathered}
   H'=G-z-3x-5/2,\quad Q=1+72/(z^2+x^2),\quad
   R'=y^2[y^2+(z^2+x^2)/2],\quad w=5/4,\\
   s=b^2uG/Q,\quad t=b^2wD,\quad
   \lambda'=24uG/(AQ),\\
   \theta=(\lambda'-H')_+/(z+3x+5/2),\qquad
   K_0=(H'-\lambda')_+ .
 \end{gathered}
\]
Take \(u\) from \(\{1,5/4,3/4,3/2\}\). Since \(\lambda'\le G\),
\(0\le\theta\le1\). With weight \(\theta\) on the first line
of (2), the shared coefficient in units of \(cb^2\) is exactly
\(K_0\). Using \(M\ge v/2\) in that line, its singleton term
combines with the other line's \(kbc\) to give
\[
 E-\lambda U-\mu U_1\le cb^2K_0 n+
 \big[(1-24w/A)b^2D-kbc-\theta\{bc(h+3q)/2+2\}\big]v.             \tag{3}
\]

Write \(K_6=b(c-1)-\min(b(c-1),(\gamma-c)p)\). The six-mode
Pauli estimate supplies a shared quadratic coefficient
\(12s[2g-(1+12K_6^2/((c-1)^2\Psi))s]\) on \(\kappa\), where
\(\Psi\ge(h^2+q^2)/6\). The factor in parentheses is at most
\(Q\), using \(K_6\le b(c-1)\); at \(c=1\) its value is one.
We discard its nonnegative linear six-mode slack.
The highest mixed contribution has quadratic coefficient
\(12t(2\Delta-t)\) on \(\kappa_1\). The Gram cross coefficient
\(s\Delta+tg-st\ge0\) because both ratios lie in \([0,2]\).
The remaining triangle Gram coefficients are nonnegative by the
same-frame matching bound. Independent leading anticommuting slots
pay \(g^2\kappa+b^4R'\kappa_1\). The six-mode square correction
already uses its separate \(P_6,P_6\) and odd-to-\(P_6\) slots.
Thus beyond \(24sU+24tU_1\) the actual defect in units of \(A\)
pays \(b^4(SP+Tv)\), where
\[
    S=\frac{G^2/12+u(2-u)G^2/Q}{A},\qquad
    T=\frac{12w(2-w)D^2+R'}{KA}.
\]
Here \(\kappa\ge P/12\) and \(\kappa_1\ge v/K\).
[Six-mode correction](rank7_six_mode_shared_probe.md) ·
[Independent leading slots](rank7_two_probe_anticommuting.md) ·
[Two excess bounds](rank7_compact_remaining_spectra.md)

In the remaining domain \(1\le c\le\min(b,9/5)\), \(1\le b\le3\).
Condition (1) gives
\[
                 b\ge B=1+\max\{y/(1+x),\,z/(1+x+y)\}.
\]
The following two rational tests imply that (3) is paid:
\[
\begin{aligned}
 B S&\ge K_0,\\
 \min(y-K_0,(9/5)(y-K_0))+
 \theta[(z+3x)/2+2/9]+B^2(S+T)&>(1-24w/A)D .                    \tag{4}
\end{aligned}
\]
Indeed for \(n=v\), after division by \(b^2 v\) the head contribution
is \(c(y-K_0)\), the singleton contribution is
\(\theta[c(z+3x)/2+2/b^2]\), and the physical contribution is
\(b^2(S+T)\). For \(0<n<v\) the left side of (3) is easier; for
\(n>v\) the first line of (4) gives \(b^2 S\ge cK_0\), paying the
increment. A stronger positive-gain comparison with factor \(A\)
than the required 168 follows on this branch.

The alternative strict weighted-split test used in the same cover is
\[
 {B^2\over168}
 \left[{12w(2-w)D^2+R'\over K}+
           \max(G^2/24,x^4/72)\right]+y>(1-w/7)D.                 \tag{5}
\]
This follows from the already proved [weighted residual](rank7_weighted_split_residual.md)
by setting \(t=w\Delta\), using \(D_0\le1,\ c\ge1,\ b\ge B\), and
dropping its independent completion and compression prices. Each box
uses either (4) or (5).

## Reproducible rational cover

For unresolved spectra the known reductions give \(z>3/5,\ x>1/5,\)
\(x<17,\ y<11/2\): use \(5g>bL,\ q<17,\ k^2\le\Delta<1800/61\).
Under the tested hypotheses \(B\le3\) implies \(z\le2(1+x+y)<50\).
The search box in order \((z,y,x)\) is
\([3/5,50]\times[0,11/2]\times[1/5,17]\).
[Compact reductions](rank7_remaining_domain.md) ·
[Fifth-probability and small-shared results](rank7_fifth_ratio_and_tight_flag_round_2026-11-18.md)

The [standard-library checker](../verification/verify_rank7_zero_nominal_payment.py)
uses exact rational endpoints. It first discards boxes where \(B>3\),
\(B^2D>1800/61\), or \(5G\le z+2y+3x\) everywhere. Otherwise it
computes lower bounds for (5) and (4). For example,
\(H'_{\rm hi}=G_{\rm hi}-(z+3x)_{\rm lo}-5/2\) gives an upper bound
on \(K_0\) and, with the upper denominator, a lower bound on \(\theta\).
All uses of \(B,S,T,D\) take the endpoint appropriate to their sign.
Boxes still undecided are bisected on a longest relative side.
The exact traversal checked **93,539 leaves**, with maximum depth 29:
976 previous-domain exclusions, 8,394 strict weighted-split leaves,
and 84,169 joint mixed leaves. Run from the project directory:

~~~text
python verification/verify_rank7_zero_nominal_payment.py
~~~

The frozen checker's SHA-256 is
\(\texttt{57809dc93d8c5e6a214511d8a30fd1d416410f1a774e0d83188cd7481aaf5dfd}\).

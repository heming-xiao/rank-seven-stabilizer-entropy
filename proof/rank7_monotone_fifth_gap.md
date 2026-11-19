# Monotone transfer in the fifth–sixth spectral gap

Normalize \(d=1\). Hold \(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a,\ p=a-b,\ c\) fixed and translate the first five probabilities by varying \(\tau=b-c\ge0\). Set \(X=h+k+q,\ Y=k+q,\ L=h+2k+3q,\ g=hq,\ \Delta=kX,\ J=Yq\). Let \(A=4242/25,\ K=5/2,\ \Lambda=200/11,\ e=c-1\). With
\[
 H=(ce-p(p+q)+\tau(e-p))_+,\quad G=(g-\Lambda H)_+,\quad
 s=uG,\quad t=w\Delta ,
\]
take \(0\le u\le3/2,\ 0\le w\le7/4\). Write \(\lambda=24s/A,\ \mu=24t/A,\ C=XYq-\lambda(Y+q)-\mu q\).
For positive-part excesses \(n,v\) put
\(M=\max(n,v/2), P=\max(n,v), Z=\max(5n/2,2v,2n+v), S=(2n+v-3M)_+\).
The compression-free direct two-probe sufficient comparison has margin
\[
\begin{aligned}
 {\cal M}_\tau={}&bcLM+Z\\
 &+[Lp(a-c)(a-1)+p^4+2(g-\lambda)p^2+(\Delta-\mu)p(a-c)+3Jp^2+Cp]P\\
 &+(\Delta-\mu)(b-1)(c-1)\max(v,n/2)+\min(q,bC)S\\
 &+\frac{g^2+12s(2G-s)+(1+\tau^2)g^2/(h^2+3q^2)}{12A}P\\
 &+\frac{R+12t(2\Delta-t)+(1+\tau^2)k^2/2}{KA}v\\
 &-(g-\lambda)cn-(\Delta-\mu)v,\qquad
 R=k^2[k^2+(h^2+q^2)/2].
\end{aligned}                                                       \tag{1}
\]
Set the displayed quotient to zero when \(h=q=0\).
This is the joint triangle comparison with zero triangle shift and unused compression. The two shifts have \(s\Delta+tg-st\ge0\), and \(C\ge0\) follows from \(g(Y+q)+\Delta q\le2XYq\) and \(84/A<1\). Nonnegativity on the six rays \((1,0),(1,1/2),(1,1),(1,2),(1,4),(0,1)\) suffices. It pays \(AE\) and hence proves optimality over every qubit cut with the \(1/101\) paired margin.
[Two-probe comparison](rank7_triangle_completion_price.md) ·
[Direct shared correction and odd-cut slots](rank7_triangle_probe_tail_equalization.md).

## Positive slope using the same five input coordinates

Assume \(1\le c\le9/5,\ g\le160c(2-c),\ L\ge7(2c-1)/5\).
For \(p\le e\) retain \(s=uG\) at each \(\tau\).
For \(p\ge e\) fix \(s=uG(\tau_0)\) at any starting point \(\tau_0\).
Then for all \(\tau\ge\tau_0\),
\[
 {\cal M}_\tau(n,v)\ge{\cal M}_{\tau_0}(n,v)+(\tau-\tau_0){\cal G}M,
 \qquad {\cal G}=cL-\frac{\Lambda}{A}(e-p)_+(4g+36c)>cL/16.       \tag{2}
\]
Thus compute \(\delta=\min_{\rm six\ rays}{\cal M}_0/M\) once
at \(b=c\). Every spectrum with \(\delta+{\cal G}(b-c)\ge0\)
is proved. In particular a nonnegative baseline gives the entire
upward interval, and a negative baseline confines any counterexample to \(b-c<-\delta/{\cal G}\).

For \(p\ge e\), \(H\) is nonincreasing. The shared payment with fixed \(s\) is nondecreasing, the debits are fixed, and all prices other than the singleton are nondecreasing. The singleton yields \(cLM\) per unit \(\tau\). The same argument transfers a compression-free rank-six shared payment when \(p\ge e\): its factor \(Q=1+12H^2/(e^2\Psi)\), with \(\Psi=e^2+(h^2+q^2+\tau^2+1)/6\), is nonincreasing. Fixing \(s\) keeps \(12s(2g-Qs)\) nonnegative and nondecreasing. When \(e=0\) use \(Q=1\).
[Rank-six correction](rank7_six_mode_shared_probe.md).

For \(p<e\), \(G\) is nonincreasing with derivative at least \(-\Lambda(e-p)\) on its differentiable pieces. Thus \(C\) is nondecreasing, together with the head and tail prices. Only the shared mixed payment and the shared debit may decrease the slope from the singleton. Since \(12s(2G-s)=12u(2-u)G^2,\ u(2-u)\le1,\ P\le2M,\ n\le M\), their total negative slope has magnitude at most \((\Lambda/A)(e-p)(4g+36c)M\). Continuity at the clipping points gives (2).

For its strict bound use \(g\le L^2/12\), which follows from \(h+3q\ge2\sqrt{3g}\).
Put \(L_0=7(2c-1)/5,\ L_1=\sqrt{1920c(2-c)}\). The loss as a fraction of \(cLM\) is at most \((\Lambda/A)e[L/(3c)+36/L]\) on \([L_0,L_1]\), a convex function of \(L\), and the bound using \(g\le160c(2-c)\) decreases for \(L\ge L_1\). At \(L_0\),
\(e[L_0/(3c)+36/L_0]\le56/75+720/91\) from \(e/(2c-1)\le4/13\) and \(L_0/c\le14/5\).
At \(L_1>26\) use \(\sqrt{1920}<44\) and \(e\sqrt{1-e^2}/c\le1/2\) to obtain the strict bound \(22/3+72/65\).
Both endpoint bounds multiplied by \(\Lambda/A\) are below \(15/16\).

The residual spectral region meets these hypotheses: the existing weighted highest-pair test forces \(g<160[1-p(a-c)-(b-1)(c-1)]\le160c(2-c)\), and the proven low-head region forces \(L\ge X>7(2c-1)/5\) on the complement.
[Residual contraction](rank7_separated_bottom_pair.md) ·
[Low-head region](rank7_two_probe_separation_and_tail_region.md).

At \((h,k,q,p,c)=(9.41,1.23,2.8,0.01,1.18)\), choose \(u=3/4,w=7/4\).
The compression-free baseline has \(-6/5<\delta<-1\), while \({\cal G}>21\).
Thus the comparison proves all \(\tau\ge7/50\) for these five fixed coordinates even though its baseline margin is negative.
[Exact checker](../verification/verify_rank7_monotone_fifth_gap.py).


## Combining both upward gap transfers

A single baseline at \(a=b=c\) suffices for a two-gap region.
For fixed \(h,k,q,c\) use (1) with \(p=\tau=0\) and write
\(\delta_0=\min_{\rm six\ rays}{\cal M}_0/M\). Put
\[
 \begin{aligned}
  \mathcal G_0&=cL-(\Lambda/A)(c-1)(4g+36c),\\
  C_{\min}&=XYq-(36/A)g(Y+q)-(42/A)\Delta q,\\
  B(p)&=pC_{\min}+p^4+Lp^3
       +(1-36/A)g\,p(2p+c-1)
       +(1-42/A)\Delta p^2+Jp(3p+2c-1).
 \end{aligned}
\]
On the domain of (2), every ordered spectrum with
\[
                \delta_0+\mathcal G_0(b-c)+B(a-b)\ge0
\]
has global order-two computational-basis optimality with the
same paired margin. This uses four input coordinates for the
baseline and explicit increments in the two remaining gaps.

First set \(p=0\) and apply (2) to reach the target \(b-c\),
using the shifts at this intermediate spectrum. Next raise
\(p\) to its true value on the same frame and keep the shifts
fixed. The direct shared coefficient \(g-\Lambda H\) is
nondecreasing in \(p\), since \(H=(b(c-1)-p(p+b-c+q))_+\).
The highest and anticommuting terms of the mixed comparison
remain available at least at their intermediate sizes. By the
exact fourth-gap transfer, the signed exterior term improves
by at least \(B(p)e'\), \(e'=1-w_{0123}\ge P\ge M\).
For this bound use \(g-\lambda\ge(1-36/A)g\),
\(\Delta-\mu\ge(1-42/A)\Delta\), \(C\ge C_{\min}\), and \(b\ge c\).
All terms of \(B\) are nonnegative. The argument uses the
fourth-gap increment only after the intermediate comparison
has been paid, so the two improvements add on the same frame.
[Signed fourth-gap transport](rank7_fourth_third_product.md).

At the earlier rational example the new baseline is
\(-4<\delta_0<-39/10\). The two increments separately
leave a negative lower bound, while their sum gives a strict
margin greater than \(6/25\) per \(M\).
[Exact two-gap check](../verification/verify_rank7_monotone_fifth_gap.py).


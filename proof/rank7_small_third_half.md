# A highest-pair comparison when the third-to-fourth gap is at most half the fifth probability

For positive ordered probabilities \((\alpha,\beta,\gamma,a,b,c,d)\),
write \(q=\gamma-a,\ p=a-b\). The sorted computational representative
is globally optimal for order-two nonlocal stabilizer Rényi entropy,
on every qubit cut, throughout \(q\le b/2\). All other ordered
probabilities, including the fourth-to-fifth gap, are unrestricted. The comparison
uses one actual highest-pair mixed shift and the true highest-pair
compression interval.

## A six-ray spectral test

Normalize \(d=1\). The [zero-shared-width theorem](rank7_zero_shared_width.md)
already covers \(\gamma\le ab\) or \(\alpha\le\beta b\).
On the remaining branch
\[
         1\le b<1+q/a\le 1+q/b\le3/2 .
\]
Use \(z=(\alpha-\beta)/b,\ y=(\beta-\gamma)/b,\ x=q/b,\)
\(G=zx,\ D=y(z+y+x),\ R'=y^2[y^2+(z^2+x^2)/2]\).
Put \(A=(101/100)168,\ K=5/2,\ w=5/4,\ \rho=1-24w/A\), and
\[
             C'=x(z+y+x)(x+\rho y).
\]
Write \(n=\nu_+\), \(v=(L_{01}-2)_+\), \(P=\max(n,v)\),
\(M=\max(n,v/2)\), \(Z=\max(5n/2,2v,2n+v)\),
\(J=(2n+v-3M)_+\). The already-covered axes allow one to focus on
\(n,v>0\).

Choose \(t=wb^2D\) for the highest mixed shift, zero other shifts,
and \(\mu=24t/A\). The completion coefficient in the signed exterior
comparison is \(C=b^3 C'>0\). Retain from its expansion the
weighted singleton, constant floor, geometric interpolation, and
the separate \(p C P\) part of completion. After dividing the
exterior and physical prices by \(b^2\), a sufficient strict test is
\[
\begin{aligned}
  \rho D v < {}&
      {b^2G^2\over12A}P
      +{b^2[12w(2-w)D^2+R']\over KA}v\\
  &+(z+2y+3x)M-Gn+{Z\over b^2}
       +\min(x/b,bC')J+p b C'P
       +{64\over A}{\sigma_1^2\over b^2}v,                         \tag{1}
\end{aligned}
\]
where \(\sigma_1=(\sqrt{\alpha\beta c}-\sqrt{\alpha\gamma ab})_+\).
Indeed the actual singleton/shared term before simplification is
\(c[(z+2y+3x)M-Gn]\). Its bracket is nonnegative since \(x\le1/2\)
and \(M\ge n\). Thus \(c\) can be lowered to one there. The
completion deficit is at least \(p(1-w_{0123})+b x_{\rm comp}\).
Its first summand pays \(p C P\); the second with the three-head
singleton increment gives \(\min(q,C)J\). Other tail-prefix prices
are nonnegative. The actual highest mixed coefficient is
\(12w(2-w)b^4 D^2\kappa_1\); the separate leading anticommuting slots
pay \(b^4G^2\kappa+b^4R'\kappa_1\). Use
\(\kappa\ge P/12,\ \kappa_1\ge v/K\). The true highest cut pays
\(64\sigma_1^2v\) and requires no crossing subtraction. There is
no shared mixed or shared compression price in (1).
[Signed singleton and completion interpolation](rank7_uniform_cut_packing.md) ·
[General-tail exterior subsidies](rank7_triangle_completion_price.md) ·
[Highest mixed and true compression](rank7_weighted_split_residual.md)

All terms are affine on sectors delimiting the six extreme rays
\[
      (n,v)=(1,0),(1,1/2),(1,1),(1,2),(1,4),(0,1).
\]
As (1) pays the enhanced factor \(A>168\), any fixed spectrum
passing the test has a positive paired-defect margin. The standard
equality and open-neighborhood transfer applies.

## Exact three-variable boxes; allowing an unequal fourth probability

On a rational slab \(\ell\le b\le u\) use \(\ell^2\) in the two
physical quadratic terms, \(u^2\) under \(Z\), and
\(\min(x/u,\ell C')\) in the interpolation. For a prescribed
upper bound \(p\le\delta\), the true highest width satisfies
\[
 {\sigma_1^2\over b^2}\ge
  { (1+x+y+z)
    [y-(u(u+\delta)-1)(1+x)-(\delta/\ell)u(u+\delta)]_+^2
     \over (1+u+\delta/2)^2(1+x+y+\delta/\ell)} .                  \tag{2}
\]
For its derivation replace \(c\) by one in the positive difference,
factor out \(\alpha/b\ge1+x+y+z\), and use the conjugate denominator
in \(\sqrt{1+x+y+p/b}-\sqrt{b(b+p)(1+x+p/b)}\).
Here \(\sqrt{b(b+p)}\le u+\delta/2\).
For a known lower bound \(p\ge\delta\), one may instead omit the
width and retain \(\delta\ell C'P\). The tied case takes \(\delta=0\)
in (2).

The [head-gap theorem](rank7_large_fifth_probability.md) already
applies when \(bc(h+4k+3q)\ge22\), since \(q\le b/2\).
The previous reductions also imply \(5G>z+2y+3x,\ x>1/5,\)
\(z>3/5,\ y<11/2,\ b^2D<1800/61\). Thus the initial box in
\((z,y,x)\) is \([3/5,22]\times[0,11/2]\times[1/5,1/2]\).
The [standard-library verifier](../verification/verify_rank7_small_third_half.py)
uses eight \(b\)-slabs with endpoints \(1+j/16,\ 0\le j\le8\).
All bounds use rational arithmetic. For instance the singleton
term is evaluated as \(z(M-xn)+(2y+3x)M\), with the upper endpoint
of \(x\) in the first factor providing a lower bound.

For \(p=0\) the exact traversal closed **44,745 leaves**, maximum
depth 23. Prior domain tests settled 4,290; (1) settled the other
40,455. Its command is

~~~text
python verification/verify_rank7_small_third_half.py tied
~~~

The checker separately completed both general-tail branches. The
spectral gap here is in units of \(d\).

| Command suffix | Fourth gap | Leaves | Maximum depth | Prior-domain exclusions | Highest mixed |
| --- | --- | ---: | ---: | ---: | ---: |
| small | \(0\le p\le1/16\) | 116,066 | 27 | 6,530 | 109,536 |
| large | \(p\ge1/16\) | 178,526 | 30 | 12,534 | 165,992 |

The small branch uses (2), and the large branch uses the linear
completion payment without any compression. No auxiliary weighted
split leaves were needed. Together these prove the full stated
spectral criterion. The checker SHA-256 is
\(\texttt{517dd88eb17bcdc15e91f057c5a907d16d1c77f6ca40eabfc50d5c51242d2db1}\).

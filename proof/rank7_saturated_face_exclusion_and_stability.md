# Exclusion of the entire saturated six-mode face and a linear Pauli estimate

November 18, 2026. No physical seven-frame lies on the packing face
\[
 d_s=D_6=D_{57}=x=0,\qquad \nu=1/2,\qquad d_1=1/4 .                  \tag{1}
\]
Equation (6) bounds the departure from disjoint Pauli supports on
every physical seven-frame by a linear combination of packing
quantities. The final section gives the strict affine separation
\(d_s+D_6+D_{57}+x+(1/2-\nu)+(2d_1-\nu)>10^{-130}\)
in every local qubit dimension \(D\ge8\). The broader optimality
question for all fourth/fifth ties remains open.
[Definition of the face and its multiple abstract feasible points](rank7_blossom_gram_witness_exclusion.md)

## Exact Pauli subgroup argument

Use \(P=\operatorname{span}(x_0,x_1,x_2)\), \(M=\operatorname{span}(x_1,x_2)\),
\(Q=\operatorname{span}(x_3,x_4)\), \(V=\operatorname{span}(x_5,x_6)\).
For a skew Pauli antiunitary \(J_a=W_a\,\mathrm{conj}\), let
\(p_{ij}=|\langle x_i,J_a x_j\rangle|^2\). The normalized sum
\(\langle f\rangle=(2/D)\sum_{a\ {\rm odd}} f(a)\) satisfies
\(\langle p_{ij}\rangle=1\) for distinct orthonormal basis vectors.

The exact flag argument on (1) gives more than the disjointness of
the three leading pair weights. Write
\[
 A=\{a:p_{01}(a)>0\},\quad B=\{a:p_{02}(a)>0\},\quad
 Q_A=\operatorname{span}(x_2,x_5),\quad Q_B=\operatorname{span}(x_1,x_6).
\]
Then \(J_a Q=Q_A\) for every \(a\in A\), and \(J_b Q=Q_B\) for
every \(b\in B\). Indeed the proof in the preceding note constructs
orthonormal \(t,\ell\) in \(Q\) with \(J_a t=-n\) the leading
kernel and \(J_a\ell=v'\in V\). In the \(01\) case its two zero
products force \(n\parallel x_2,\ v'\parallel x_5\). The \(02\)
case interchanges \(1,2\) and \(5,6\).
[Pointwise flag and its final two products](rank7_blossom_gram_witness_exclusion.md)

Since each \(L_{0i}-2\le1/3\), their sum \(1/2\) forces both
excesses to be at least \(1/6\). The individual Pauli bound
\((L_{0i}-2)_+\le(5/2)\kappa_{0i}\) therefore gives
\(\kappa_{01},\kappa_{02}>0\). Each positive-support set carries
ordinary sum \(D/2\) of numbers at most one, with at least one
strictly between zero and one. Consequently \(|A|,|B|> D/2\).
[Individual bound](rank7_highest_pair_geometry_five_halves.md)

Let \(H\) be the binary group of Pauli labels whose unitary representatives
preserve \(Q\). The product of two antiunitaries mapping \(Q\) to the
same plane differs only by phase from the unitary labelled by their
binary difference, when the first antiunitary is inverted. Thus each
of \(A,B\) is contained in one coset of \(H\), and \(|H|\ge D\).
The restriction of the symplectic form to \(H\) has rank at most two.
Indeed a subgroup of symplectic rank \(2k\) has irreducible Pauli
blocks of dimension \(2^k\), and \(Q\) has dimension two. The size
bound \(|H|\le2^kD\) follows by adjoining one generator of each
symplectic pair to the radical to obtain an isotropic subgroup.

If \(H\) is isotropic it is maximal, of order \(D\). Then \(Q\) is
spanned by two joint eigenlines. Those lines are two points of a
stabilizer basis, and the Pauli translation exchanging them also
preserves \(Q\) and lies outside its diagonal subgroup. Thus this
case cannot be the full group \(H\).

It remains that \(k=1\).

- If \(|H|=D\), its radical has size \(D/4\). The invariant
  plane \(Q\) is a single irreducible two-dimensional module, hence
  it belongs to one joint radical-character block of dimension four.
  In a coset \(a+H\), the parity of \(a+v\) and \(a+v+r\) differs
  by \(q(r)+[a,r]\) for \(v\in H\) and radical \(r\), where \(q\)
  is Pauli transpose parity. If this equals one, precisely half
  the coset is odd, incompatible with either support size. Each
  coset in question therefore has \(q(r)+[a,r]=0\) on the radical.
  This says exactly that \(J_a W_r J_a^{-1}=W_r\) for Hermitian
  representatives; conjugation of the real eigenvalues does nothing.
  The two cosets thus preserve every radical-character block. The
  one block containing \(Q\) must then contain the three mutually
  orthogonal two-planes \(Q,Q_A,Q_B\), an impossibility.
- If \(|H|=2D\), its radical has size \(D/2\), and \(Q\) is an
  entire rank-two character block. Within the coset containing \(A\),
  all \(J_a\) shift every radical character by the same character
  \(\chi_A\), using the formula \(q(r)+[a,r]\) just given. The
  shift is nontrivial since it sends \(Q\) to \(Q_A\perp Q\). The
  other support analogously sends \(Q\) to a rank-two block \(Q_B\).
  Hence \(J_a x_1\) belongs to a fixed block \(Q_C\perp Q_B\)
  for all \(a\in A\). The normalized skew frame identity gives
  \[
   1=\langle\mathbf 1_A|\langle x_0,J_a x_1\rangle|^2\rangle
       \le\langle|\langle P_{Q_C}x_0,J_a x_1\rangle|^2\rangle
       \le\|P_{Q_C}x_0\|^2 .
  \]
  Thus \(x_0\in Q_C\) and \(x_1\in Q_B\) have opposite eigenvalues
  for a radical Pauli. The opposite-eigenspace pair inequality
  \(L_{01}\le2\) contradicts \(L_{01}-2\ge1/6\).
  [Opposite Pauli sectors](rank7_five_set_structured_probe.md)

## A linear stability estimate for Pauli overlap

Write \(Y=Q+V,\ S=P+Y\);
\(A_i=w_{012i}\), \(W_{ijk}=\sum_{\ell\in S}w_{ijk\ell}\), with
repeated entries zero. Define the nonnegative observables
\[
\begin{aligned}
 A_0'&=1-A_3-A_4,&
 T_Q&=\sum_{\{i,j\}\subset\{0,1,2\}}w_{ij34},&
 T_Y&=\sum_{3\le i<j<k\le6}w_{0ijk},\\
 C_Q&=\sum_{j=1,2;\,i=3,4}(1-W_{0ji}),&
 C_*&=(1-W_{015})+(1-W_{026}),\\
 E_0&=A_0'+T_Q+T_Y+C_Q,& E_f&=E_0+C_* .
\end{aligned}                                                        \tag{2}
\]
The sums of the \(W_{ijk}\) are over labels in the seven-dimensional
support chosen in the statement. Put \(p=p_{01}+p_{02},\ r=p+p_{12}\).
For all physical frames,
\[
 \langle p\,p_{12}\rangle\le45E_0,\qquad
 \langle p_{01}p_{02}+p\,p_{12}\rangle\le1560E_f.                    \tag{3}
\]
Here is a pointwise proof with all constants. At a fixed odd label
let \(\omega(u,v)\) denote its skew two-form, and let
\(F(u,v,s,y)\) be the four-Pfaffian. For an orthonormal triple,
the norm of its one-leg completion is the square root of the sum
of the three squared pair entries: the completion vector is a
signed combination of \(Ju,Jv,Js\), with the opposite pair
entries as coefficients and the conjugations dictated by the
inner-product convention. This vector is orthogonal to the triple.
The phase choices below only affect signs or phases of coefficients.

Let \(a,b,c,d_0,e\) be the five nonnegative pointwise errors
obtained respectively from the following squared norms:

- \(a=r\|(I-Q)t\|^2\), where \(n\) is the unit leading kernel and
  \(t=Jn\). The term is zero at \(r=0\).
- \(b=\sum_{i<j\le2}|F(x_i,x_j,x_3,x_4)|^2\).
- \(c\) is the sum of squared outside-\(S\) completion norms for
  \(013,014,023,024\).
- \(d_0=\sum_{3\le i<j<k\le6}|F(x_0,x_i,x_j,x_k)|^2\).
- \(e\) is the sum of squared outside-\(S\) completion norms for
  \(015,026\).

By the [squared-Pfaffian identity](rank7_triangle_quantitative_rigidity.md)
and the full one-hole Parseval identity, their normalized means are
respectively \(3A_0',3T_Q,3C_Q,3T_Y,3C_*\).
Write \(\xi_0=a+b+c+d_0,\ \xi=\xi_0+e\).

Suppose \(p>0\), since the claimed overlaps vanish otherwise. Set
\(d_t=\operatorname{dist}(t,Q)\). If \(d_t^2>1/4\) the sum of overlaps
is at most \(p\le r\le4a\), so we may assume \(d_t^2\le1/4\).
Let \(t_q\) be the normalized projection of \(t\) to \(Q\) and choose a unit
\(\ell\in Q\ominus\mathbb C t_q\).
Put \(L=\|P J\ell\|\). In \(F(n,u,t_q,\ell)\) for \(u\perp n\) in \(P\)
the only possible term has modulus
\(\sqrt{1-d_t^2}\,|\omega(u,\ell)|\). Thus \(L\le2\sqrt b/\sqrt3\).
Also \(\|QJ\ell\|\le d_t\) since \(J\ell\perp t,\ell\).
Choose \(u\in M\) with \(|\omega(x_0,u)|=\sqrt p\).
Taking the outside component of the completion of \(0u\ell\) gives
\[
   \sqrt p\,\|(I-S)J\ell\|\le\sqrt c+L .
\]
The other two terms combine into \(Jx_0,Ju\) with squared coefficient
sum at most \(L^2\). For \(d_v=\operatorname{dist}(J\ell,V)\) this yields
\[
 p d_v^2\le p(L^2+d_t^2)+(\sqrt c+L)^2
       \le a+(11/3)b+(7/3)c .                                       \tag{4}
\]
If \(d_v^2>1/4\), the overlap sum is at most \(p<15\xi_0\).

Otherwise let \(v'\) be the normalized projection of \(J\ell\) to \(V\),
\(v''\) its orthogonal unit partner, and \(d_n=|\langle x_0,n\rangle|\).
Expanding \(t\) along \(t_q\), and then \(F(x_0,t_q,\ell,v')\),
gives
\[
 d_n\le d_t+[\sqrt{d_0}+d_t(L+d_v)]/\sqrt{1-d_v^2}.
\]
Indeed \(|\omega(\ell,v')|=\sqrt{1-d_v^2}\);
\(|\omega(t_q,v')|,|\omega(t_q,\ell)|\le d_t\) because \(Jt=-n\)
is orthogonal to both test vectors; and
\(|\omega(x_0,v')|\le d_v\) because \(J(J\ell)=-\ell\perp x_0\).
Since \(L\le d_v\le1/2\), Cauchy–Schwarz gives
\(p d_n^2\le6(a+d_0)\). Here
\((1+2/\sqrt3)^2+4/3<6\).
As \(p_{12}=r d_n^2\), in all branches \(p\,p_{12}\le15\xi_0\).

Let \(m\) be the normalized projection of \(n\) to \(M\), and let
\(z\) be its orthogonal unit partner. The projection exists since
\(p>0\). One has \(\omega(x_0,m)=0\), \(|\omega(x_0,z)|=\sqrt p\).
Put \(\delta^2=d_n^2+d_t^2+d_v^2\); (4) gives \(p\delta^2\le8\xi_0\).
If \(\delta>1/4\), the combined overlap is at most \(p\le128\xi_0\).
Assume henceforth \(\delta\le1/4\). The exact invariant four-plane
\(K=\operatorname{span}(n,t,\ell,J\ell)\) is within projection distance
\(\delta\) of the orthonormal four-plane
\(K'=\operatorname{span}(m,t_q,\ell,v')\). Indeed the squared
leakages of the four orthonormal vectors of \(K\) from \(K'\) sum
to at most \(\delta^2\). Consequently \(J\) maps either \(K'\) or
its orthogonal complement back to itself up to leakage norm \(2\delta\).

Inside \(S\) let \(G=\operatorname{span}(x_0,z,v'')=S\ominus K'\).
Its volume has total completion norm at least \(\sqrt p\), and the
completion is this norm times the image under \(J\) of its unit
kernel vector in \(G\). It is orthogonal to \(G\), so its outside
norm is at least \(\sqrt p\sqrt{1-4\delta^2}\).
Each of the three other triples formed using \(x_0\) and one choice
from each pair \((m,z)\) and \((v',v'')\) has outside completion norm
at most \(4\delta\). For one \(K'\) leg, the \(G,G\) pair contributes
at most \(2\delta\) outside, and the other two coefficients have
joint norm at most \(2\delta\) by the \(K'\)-to-\(G\) leakage.
For the triple with two \(K'\) legs, \(|\omega(m,v')|\le2\delta\)
by comparison with the differently paired \(n,J\ell\), and
\(\omega(x_0,m)=0,\ |\omega(x_0,v')|\le2\delta\).

Set \(s=|\langle z,x_1\rangle|^2,\ t'=|\langle v'',x_5\rangle|^2\).
Expanding both \(015\) and \(026\) in the four triple volumes just
used is an orthonormal two-row coefficient matrix, so the three
non-\(G\) columns have combined output norm at most \(4\sqrt3\,\delta\).
With \(B=s t'+(1-s)(1-t')\ge s(1-s)\), the triangle inequality gives
\[
 \sqrt p\sqrt{1-4\delta^2}\sqrt B\le\sqrt e+4\sqrt3\,\delta .
\]
Now \(p_{01}p_{02}=p^2s(1-s)\). The preceding estimates imply
\[
 p_{01}p_{02}\le(4/3)\,p(\sqrt e+4\sqrt3\,\delta)^2
 \le (4/3)(1+384)\xi .
\]
Adding \(p\,p_{12}\le6\xi_0\) on this branch gives a total at most
\(520\xi\). All earlier branches obey this bound as well. Averaging
proves (3).

## Interface with the signed packing comparison

Let \(u=1-2\nu-x,\ m_0=2d_1-\nu\). Summing the four directed rows
that count 0 and omit a specified tail gives \(T_Y\le u\). Write
\(\theta_i=2-\sum_{I\ni0,\ I\not\ni i}w_I\ge0\).
Then \(L_{0i}=1+\nu+x+T_Y+\theta_i\), and
\[
 W_{01i}+W_{02i}=L_{0i}+A_i-
       \sum_{\substack{J\subset Y,\ |J|=3\\i\in J}}w_{0J}.
\]
Summing at \(i=3,4\) gives \(C_Q\le u+A_0'\). The complement pair
row gives \(T_Q\le A_0'\). The eight-row price for
\(\nu+2W_1^6\) includes both completion rows of \(015,026\); hence
\(C_*\le m_0\). In particular
\[
           E_0\le3A_0'+2u,\qquad E_f\le3A_0'+2u+m_0,\qquad
           A_0'\le D_{57}-x .                                         \tag{5}
\]
By the exact Gram identities for incident edges, (3) implies
\[
 \boxed{\quad \eta\ge\kappa+\kappa_{12}-90E_0,\qquad
          \eta\ge(2/5)\nu+\kappa_{12}-3120E_f .\quad}                  \tag{6}
\]
The second inequality uses \(\kappa_{01}+\kappa_{02}\ge(2/5)\nu\).
These are necessary linear comparisons on arbitrary physical frames,
including those away from (1).

## A dimension-independent affine separation of the whole face

All six terms of the following affine functional are nonnegative:
\[
 {\cal F}=d_s+D_6+D_{57}+x+(1/2-\nu)+(2d_1-\nu).
\]
We claim that every physical frame has \({\cal F}>10^{-130}\).
In particular \({\cal F}\ge10^{-130}\) survives arbitrary convex
mixtures and their closure, even when the ambient dimension varies.
Only the absolute separation is claimed. The numerical constant
allows deliberately generous intermediate bounds.

Assume \({\cal F}\le10^{-130}\). From (5), \(A'_0\le{\cal F}\),
\(u\le2{\cal F}\), \(m_0\le{\cal F}\), whence
\(\langle\xi\rangle=3E_f\le24{\cal F}\).
Also \(v_{01},v_{02}\ge1/6-{\cal F}\), as each is at most \(1/3\).
Set \(\sigma=10^{-20}\), \(\tau=10^{-100}\).
Call a label a candidate if \(p\ge\sigma,\ \xi\le\tau\).
For a candidate the branches \(d_t^2>1/4\), \(d_v^2>1/4\) and
\(\delta>1/4\) are impossible: in these branches the proof above
gives respectively \(p\le4\xi,\ p\le15\xi,\ p\le128\xi\).
For the remaining branch it gives
\[
 \delta\le\sqrt{8\tau/\sigma}<3\cdot10^{-40},\qquad
 B\le {4\over3\sigma}(\sqrt{\tau}+4\sqrt3\,\delta)^2<10^{-56}.
\]
Put \(\mathcal A=\{\text{candidates with }s\ge1/2\}\) and let
\(\mathcal B\) be the other candidates. On \(\mathcal A\) one has
\(t'\le2B,\ 1-s\le2B\); on \(\mathcal B\), \(1-t'\le2B,\ s\le2B\).
Consequently, with \(\epsilon=10^{-26}\),
\[
 \|J_a Q J_a^{-1}-Q_A\|<\epsilon\quad(a\in\mathcal A),\qquad
 \|J_b Q J_b^{-1}-Q_B\|<\epsilon\quad(b\in\mathcal B).              \tag{7}
\]
Here and below we use the operator norm for differences of orthogonal
projections. Indeed \(Jt_q\) has line distance at most \(d_t+d_n\)
from \(m\), and \(J\ell\) has line distance \(d_v\) from \(v'\).
The projection distance of \(JQ\) to \(\operatorname{span}(m,v')\)
is at most \(\sqrt{(d_t+d_n)^2+d_v^2}\le\sqrt2\,\delta\), by
summing the squared leakages of its orthonormal basis. Replacing
the \(M,V\) lines with their indexed basis lines costs at most
\(\sqrt{2B}\) in projection distance, since the blocks are orthogonal.

The small-\(p\) tail must be controlled without the ambient dimension
in the denominator. Write \(R=M+V\). In every label of the good
branch \(\delta\le1/4\), the preceding trace estimate gives
\(\operatorname{Tr}(R J_a Q J_a^{-1})\ge2-2\delta^2\ge1\).
The Pauli unitary twirl, applied to the conjugate of \(Q\), gives
\(\sum_{\rm all\ labels}\operatorname{Tr}(R J_a Q J_a^{-1})=8D\);
hence at most \(8D\) labels lie in that branch. Set the mass of
a function on any label set to its normalized skew sum. The \(p_i\)
mass lost by taking \(\mathcal A\) for \(i=01\) and \(\mathcal B\)
for \(i=02\) is bounded as follows:

- On the three bad branches, \(p_i\le p\le128\xi\).
- Inside the good branch with \(p<\sigma\), the normalized mass is
  at most \(16\sigma\). For \(\xi>\tau\) the normalized *count*
  is at most \(24{\cal F}/\tau\).
- On the candidate set of the opposite orientation, \(p_i\le2B\);
  here the normalized count is at most \(16\).

Their sum is at most
\(128\cdot24{\cal F}+16\sigma+24{\cal F}/\tau+32\cdot10^{-56}
<10^{-17}\). Write \(l=10^{-17}\). Both retained masses are
at least \(1-l\). Each retained normalized count is at least
\(1+\kappa_i-2l\), since \(1\ge p_i+p_i(1-p_i)\) and removal
loses at most twice the deleted mass. By the individual five-halves
bound \(\kappa_i\ge (2/5)(1/6-{\cal F})\). Therefore
\[
                 |\mathcal A|,\ |\mathcal B|>0.52D.                 \tag{8}
\]

Choose \(a_0\in\mathcal A,\ b_0\in\mathcal B\) and put
\(T=(\mathcal A+a_0)\cup(\mathcal B+b_0)\). It contains zero.
Every \(t\in T\) moves \(Q\) by projection distance at most
\(2\epsilon\), by (7), since the inverse of an odd \(J\) is itself
up to a scalar. Every \(t\in10T\) then moves it by at most
\(20\epsilon\). The Pauli twirl gives
\(\sum_t\operatorname{Tr}(QW_tQW_t^\dagger)=4D\), hence
\[
            |10T|\le {2D\over1-(20\epsilon)^2}<2.01D .
\]
In the Cayley graph generated by \(T\), a vertex at distance nine
would yield four disjoint translates of \(T\) in \(10T\), using
the vertices at distances \(0,3,6,9\) on a shortest path.
This contradicts (8). Therefore \(\langle T\rangle=8T\); every
element of that group moves \(Q\) by at most \(16\epsilon\).
Average \(Q\) under those conjugations. The average differs from
\(Q\) by at most \(16\epsilon\) in norm. Its spectral projection
\(Q_*\) above \(1/2\) has rank two and distance at most
\(32\epsilon\) from \(Q\), using eigenvalue perturbation followed
by the triangle inequality. In particular \(\langle T\rangle\)
lies in the full unitary Pauli preserving group \(H\) of \(Q_*\);
the two good supports are subsets of two \(H\)-cosets.

The same representation argument as in the exact proof leaves
\(|H|=D,2D\) with symplectic rank two. In the first case the
odd majority (8) forces both cosets to preserve each common
rank-four radical-character block. The block containing \(Q_*\)
thus contains two image planes within \(33\epsilon\) of \(Q_A,Q_B\),
and is itself within that leakage of each basis vector of \(Q\).
The trace of its projection on the six orthogonal vectors of
\(Q+Q_A+Q_B\) would be at least \(6(1-(33\epsilon)^2)>4\).

In the second case \(Q_*\) is a full radical block. Its two
fixed image blocks \(Q_A^*,Q_B^*\) are within \(33\epsilon\)
of \(Q_A,Q_B\), respectively. The shift of the first coset is
nontrivial, since \(Q_A\perp Q\) and
\(\|Q_A^*-Q_A\|+\|Q_*-Q\|<1\). Thus the first coset maps
\(Q_B^*\) to a different fixed block \(Q_C^*\).
Write \(y=P_{Q_B^*}x_1\), so \(\|x_1-y\|\le33\epsilon\).
On \(\mathcal A\), \(J_a y\in Q_C^*\). By the triangle inequality
in normalized square sum on \(\mathcal A\) and skew Parseval,
\[
 \sqrt{1-l}\le\|P_{Q_C^*}x_0\|\,\|y\|+\|x_1-y\|.
\]
It follows that the squared leakage of \(x_0\) from \(Q_C^*\) is
at most \(l+66\epsilon<10^{-16}\). Normalize the projections of
\(x_0,x_1\) into \(Q_C^*,Q_B^*\) to unit vectors \(x'_0,x'_1\).
Their total norm change is below \(3\cdot10^{-8}\).
The two unit vectors lie in opposite eigenspaces of a radical Pauli.

For clarity the original five tail vectors may be held fixed for
this last comparison. Project them perpendicular to \(x'_0,x'_1\):
the resulting frame operator on the projected span is bounded by the
identity, and its second exterior power is bounded by the exterior
projection of a space of dimension at most five. The opposite-sector
estimate therefore bounds the normalized pair value for \(x'_0,x'_1\)
and the original tail by \(2\). Also the normalized norm
\(q^{-1/2}\|\Pi_F(y_0\wedge y_1\wedge y_2\wedge y_3)\|\) is at most
\(\prod_i\|y_i\|\). This follows by Gram orthogonalization and the
four-vector one-hole bound \(w_I\le1\). Each of the ten squared
summands in \(L_{01}\) hence changes by at most twice the two-vector
total norm change, by multilinearity. This gives
\(L_{01}\le2+6\cdot10^{-7}\), contradicting
\(L_{01}-2\ge1/6-{\cal F}\). This proves the affine separation.

# The printed boxes compute the circle-compressed trace

**Ordinary-mathematics replacement for (12.1.1.2), PDF p. 499.** Let
$G=C_{\mathbb Q(i)}$, and let $H$ be the image of the Archimedean-only
$S^1$. Use the literal global quotient boxes $E_k=\overline U_k$ of
(A.5.2.19)–(20) and (A.5.2.23)–(24), pp. 576–577, and Definition
A.5.2.18(2), p. 578, on the tail $k\ge2$. Let $\mu$ be Haar measure,
$w$ a strictly positive continuous radial weight, and $\lambda=w\mu$.
For every trace-class operator $T$ on $L^2(G,\lambda)$ and every
representative of its $\lambda$-relative Hilbert–Schmidt kernel $k_T$, put
$$
 d_k(x)=\frac{1}{\mu(E_k)^2}
    \int_{xE_k\times xE_k} k_T(y,z)\,d\mu(y)\,d\mu(z).
$$
Then $d_k$ has an almost-everywhere limit $d\in L^1(G,\lambda)$ and
$$
 \int_G d\,d\lambda=\operatorname{Tr}(P_HTP_H),\qquad
 \operatorname{Tr}(T)-\int_G d\,d\lambda
   =\operatorname{Tr}((1-P_H)T(1-P_H)),
$$
where $P_H$ is averaging with probability Haar on $H$. The same theorem
holds for every strictly positive continuous **$H$-invariant** weight.
The almost-everywhere limit and its integral are independent of the
permitted subgroup base and section. The limit belongs to $L^1$;
convergence in $L^1$ norm is not claimed. No Lean declarations are used
or added.

## Literal boxes on the quotient

Use the [accepted angular source check](trace-spectral.md#the-averaging-boxes-must-actually-shrink)
(at `a0724c05f93bbb4a1bb5883785f5bb9923202b47`) for the full inverse
image of the Archimedean logarithm, the norm and class conventions, and
the Haar product averaging in Definition 12.1.1.1, pp. 498–499. For
$\mathbb Q(i)$ the logarithmic sum is empty, so the Archimedean factor
is the full $S^1$. On p. 577, Lemma A.5.2.17(1) uses a decreasing
compact open subgroup identity base $B_k$ of the finite unit group, a
continuous homomorphic section $\tau$ of the norm, the interval
$I_k=(1-1/k,1+1/k)$, and images in $G$. In particular $E_k$ is
$H$-saturated, not a choice of one point in each $H$-coset.

Write $K=\prod_{v<\infty}\mathcal O_v^\times$ and let $D$ be the
image of $\mathbb Z[i]^\times$ in $K$. Since $\mathbb Z[i]$ is Euclidean,
a generator of the finite valuation ideal reduces every idele to the
open stage $\mathbb C^\times\times K$. The projection from that stage
to $G$ is open and surjective, with kernel the diagonal Gaussian units.
The map $(z,u)\mapsto (\log|z|^2,uD)$ on this stage is continuous,
open, and surjective. Its kernel consists of the product of the
Archimedean-only circle and the diagonal Gaussian units. It follows that
$Q=G/H\simeq \mathbb R\times K/D$ as topological groups; the first
coordinate is log idelic norm. Here $H$ embeds in $G$: A diagonal unit
with all finite entries $1$ must be $1$.

Let $\pi:G\to Q$. The group $K/D$ is profinite: The images of compact
open subgroups of $K$ are compact open subgroups and give an identity
base by continuity and openness of the quotient map. The finite
coordinate of the composition of $\tau$ with the two quotient maps is
therefore trivial by connectedness of $\mathbb R_{>0}$, since the
composed map sends $1$ to the identity. The first coordinate is
$\log t$ at norm $t$. Thus the **actual** sets for any allowed choices are
$$
 V_k=\pi(E_k)=J_k\times L_k,\qquad
 J_k=\log I_k,\qquad L_k=B_kD/D.
$$
They are nested, open, relatively compact, and shrink to the identity
as a neighborhood base in both coordinates. No injectivity assumption
on $B_k\to K/D$ is needed. With probability Haar on $K$ and
$K/D$, the subgroup mass satisfies
$m_{K/D}(L_k)=[D:D\cap B_k]m_K(B_k)$ by the cosets in $B_kD$.
Haar $\nu$ on $Q$ has product form up to a constant; since $L_k$ is a
subgroup and $J_k$ an interval,
$$
 \nu(V_kV_k^{-1})=2\nu(V_k),\qquad
 \nu(V_kV_k^{-1}V_k)=3\nu(V_k),\qquad 0<\nu(V_k)<\infty.
$$
This verifies the shrinking and doubling conditions recalled in
Definition 12.1.1.1, p. 498, on $Q$. The literal norm intervals need not
be invariant under inversion, and no comparison of $\nu(V_k)$ with
$\nu(V_{2k})$ is necessary.

## Disintegrate both kernel variables

Let $dh$ be probability Haar on $H$ and set $\nu=\pi_*\mu$.
The quotient by the compact group is proper, so this pushforward is a
locally finite Haar measure. Haar disintegration reads
$$
 \int_G f\,d\mu=\int_Q\int_H f(xh)\,dh\,d\nu(\pi x).
$$
Indeed, the inner integral is independent of the representative, and
averaging over $H$ preserves the integral by translation invariance
and Tonelli. Since $w$ descends to a positive continuous $w_Q$, the
same formula holds for $\lambda$ and $\lambda_Q=w_Q\nu$. Pullback
$J:L^2(Q,\lambda_Q)\to L^2(G,\lambda)$ is an isometry. Its adjoint
averages over the fibers, so $J^*J=1$ and $JJ^*=P_H$.

With $S=J^*TJ$, independent averaging in the two fibers gives
$$
 k_S(\pi x,\pi y)=\int_{H\times H} k_T(xh,yh')\,dh\,dh'.
$$
Jensen and disintegration give $\|k_S\|_{L^2(\lambda_Q^2)}\le
\|k_T\|_{L^2(\lambda^2)}$. To identify the operator, pair the right-hand
kernel with $\overline{f(\pi x)}g(\pi y)$, for $f,g\in L^2(\lambda_Q)$.
The product is absolutely integrable by Cauchy–Schwarz on $G\times G$,
and disintegration gives exactly $\langle Jf,TJg\rangle$ (pairing
linear in the second slot). This does not assume either positivity or
commutation of $T$ with $P_H$. Since $E_k=\pi^{-1}(V_k)$, we have
$\mu(E_k)=\nu(V_k)$ and for every center $x$, each normalized product
average of $k_T$ equals the corresponding quotient average of $k_S$ on
$\pi(x)V_k\times\pi(x)V_k$. All box integrals exist: The weights are
bounded below on the compact closures and the kernels are locally Haar
integrable. The same identification holds with independent centers.

## Differentiation and trace

Let $A_k$ denote normalized Haar averaging on $xV_k$ and set
$Mf=\sup_{k\ge2} A_k|f|$. A compact subset of $\{Mf>a\}$ is covered
by finitely many open translates with average $>a$. From that cover
choose disjoint translates greedily in increasing order of $k$. If a
translate meets one already selected at index $j\le k$, it lies in
that selected translate enlarged to $V_jV_j^{-1}V_j$ because
$V_k\subset V_j$. The tripling ratio and disjointness give
$\nu(Mf>a)\le3\|f\|_1/a$ by inner regularity. Applying this weak bound
to $|f|\mathbf1_{|f|>a/2}$ and integrating in $a$ yields
$\|Mf\|_2^2\le24\|f\|_2^2$. Shrinking gives pointwise convergence of $A_k f$
for $f\in C_c(Q)$; the strong bound and density imply $A_k f\to f$
almost everywhere for all $f\in L^2(Q,\nu)$. In the density step,
$\limsup_k |A_k f-f|$ is bounded by $M(f-g)+|f-g|$ for $g\in C_c(Q)$,
whose $L^2$ norm can be made arbitrarily small.

Apply the [singular-value diagonal argument](trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal)
on $Q$. Conjugate $S$ by multiplication by $\sqrt{w_Q}$ to act on
$L^2(Q,\nu)$ with kernel $b=\sqrt{w_Q}\,k_S\,\sqrt{w_Q}$, where the
multipliers act in the first and second variables respectively. Write
its singular-value expansion $b=\sum_j s_j u_j\otimes\overline{v_j}$
with unit singular vectors and $\sum_j s_j<\infty$. The integrable
majorant $F=\sum_j s_j Mu_j Mv_j$ bounds the normalized absolute
product averages of $b$; this follows first for finite sums, then by
local $L^1$ convergence on each product box. The corresponding series
tails tend to zero almost everywhere. By one-variable differentiation
of the singular vectors the diagonal product averages of $b$ converge
to $\sum_j s_j u_j\overline{v_j}$, whose integral against $\nu$ is
$\operatorname{Tr}(S)$ by trace-norm summation. Dividing by the two
continuous square-root factors changes the diagonal limit by precisely
$1/w_Q(x)$: The error is bounded by the oscillation of their reciprocal
product on the shrinking product box times $F(x)$. Consequently the
limit for $k_S$ is in $L^1(\lambda_Q)$ and integrates to the same trace.
The singular-value formula yields the same limit for any allowed bases.
Pull it back to $G$, using disintegration for the null set and integral.
Finally $JSJ^*=P_HTP_H$, which has trace $\operatorname{Tr}(S)$,
and the off-diagonal blocks of $T$ have zero trace in the orthogonal
decomposition by $P_H$.

The same argument applies if one uses the **Haar-relative** kernel
$w(y)k_T(x,y)$ instead: The factor $w(y)$ survives fiber averaging,
and on the quotient it changes the limit by $w_Q$ by the same
oscillation bound. Integrating against $\mu$ then gives the same
compression trace. This is a conversion for a given operator, not a
reading of the kernel convention in Chapter 10. The disintegration and
singular-value steps work for any compact subgroup with saturated
boxes and a quotient family with the same shrinking and maximal
estimates. The calculation of those quotient boxes here is specific
to $\mathbb Q(i)$.

**Why the convergence is only asserted almost everywhere.** Take
$t=\log N(x)$, $w=e^{t^2}$, and the radial rank-one vector
$f(t)=e^{-t^2/2}/(1+|t|)$. Its weighted square is integrable because
the norm-one factor is compact. For any fixed $k\ge2$ the normalized
Haar average of $f$ includes shifts on a subinterval
$[-b,-a]\subset J_k$ with $b>a>0$. For large positive $t$ this
contribution is bounded below by a positive constant times
$e^{-(t-a)^2/2}/(1+t)$. The averaged rank-one diagonal is the square
of this one-variable average and is not in $L^1(w\mu)$ at that $k$.
Its pointwise limit $|f|^2$ is integrable and has the stated trace.

## Chapter 12 interface

The displayed right sides of (12.1.1.20)–(21), pp. 502–503,
use a cutoff times the geometric diagonal and the uncut spectral
diagonal, respectively. **Given** the corresponding trace-class
operators and the correct Haar-relative kernels, the literal averages
compute the traces of their $H$-invariant compressions. For the
geometric expression one can apply the result directly to the
localized operator with kernel $\rho(x)k^{\rm geom}(x,y)$.
The smooth cutoff is radial by Definition 9.3.3.1(2), p. 427. Where
$\rho(x)\ne0$, divide by $\rho$ locally on the quotient to recover the
printed cutoff-times-diagonal form: This continuous inverse multiplier
near the center is justified by the absolute-average bound. On the
zero set the localized diagonal is zero almost everywhere: The
localized compressed operator has range supported on $\{\rho\ne0\}$,
so every output singular vector of nonzero singular value vanishes
almost everywhere on $\{\rho=0\}$. This justifies setting the
cutoff-times-diagonal to zero there, without requiring the uncut
diagonal to exist there. Equivalently, use the averaged kernel of the
localized operator directly. This does not require a global trace-class
claim for the uncut geometric operator.

For either identified operator $T$, the premise needed to recover its
full trace is $\operatorname{Tr}((1-P_H)T(1-P_H))=0$, not just
commutation with $P_H$. The preceding rank-one checks are the two
extremes: The weight-four test lies in $\ker P_H$, and the radial test
lies in $\operatorname{ran} P_H$. No vanishing or nonvanishing of the
omitted trace is asserted for the manuscript's operators. The actual
weighted-kernel and operator-order identification, and compatibility
with the local-to-global diagonal, remain separate.

**Review evidence.** The worker and independent reviewer
`quotient-review` (`NLmMnQW`, transcript in Yah session
`01a20258-26ed-797b-80e3-8e7040cdae90`) used the pinned PDF. The reviewer
independently inspected rendered crops of the subgroup and section
hypotheses, (A.5.2.24) and the global quotient-image clause on p. 577,
and Definition A.5.2.18(2) on p. 578. The earlier Archimedean box,
class, norm, and averaging readings are inherited from the accepted
angular note, not presented as new visual reviews. The worker also
inspected rendered crops of (12.1.1.20)–(21), pp. 502–503, and the
norm-fiber cutoff condition of Definition 9.3.3.1(2), p. 427. The
reviewer separately checked the exact quotient images and volume
ratios, finite-direction differentiation, kernel and trace calculation,
cutoff support argument, and counterexample to $L^1$-norm convergence.
The review did not identify the actual Chapter 12 kernels.

**Next bounded check:** For the spectral operator in (12.1.1.21),
check whether a test in the weight-four angular isotype makes the
actual spectral operator supported on $\ker P_H$. Follow the quotient
factorization on p. 459, (10.4.2.5), and the homogeneous-test trace on
p. 454, (10.3.2.5), both mapped provisionally. This would reduce the
omitted trace to the full scalar trace on that test without using the
disputed kernel identification. A nonzero evaluation of that scalar
would still be a separate check.

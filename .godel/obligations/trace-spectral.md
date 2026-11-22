# Trace formula: Spectral input to the final comparison

**Status: Provisional extraction of the [digest-matched edition](../sources/masullo/README.md), with an independent Yah text-only review of the cited spectral interfaces.** No visual attestation or Lean result. Page numbers are PDF ordinals.

The [final scalar comparison](trace-assembly.json) needs (12.5.1.4), p. 520, for the same smoothed geometric diagonal as the local evaluation. The two references on p. 520 do different jobs:

- **Spectral trace:** Theorem 10.4.2.8, pp. 463–464, concerns the order $M_\rho A(\varphi)P_a^{\mathrm{spec}}$, not the projection-after-convolution order in Theorem 10.4.2.2. Its stated $s\ge 0$ does not meet $s>1$ in its cited trace formula, Theorem 10.3.2.1 (pp. 453–455), or $s\ge 3$ in the kernel definition. Page 464 n. 8 asks for completion. Once nuclearity of the **correct operator** is known, however, the cutoff limit follows from a trace-ideal argument below.
- **Geometric kernel:** Definition 10.4.3.7, pp. 473–474, subtracts a spectral kernel from $\varphi(xy^{-1})$. An almost-everywhere representative of a product kernel does not determine its diagonal values. Theorem 12.1.1.3, pp. 502–503, addresses this in the singleton-strip construction of Definition 10.4.3.2 (pp. 470–471), in the other operator order. The general-strip calculation needs its own operator identification and measure conversion; see below.

## Which operator does the series represent?

**Provisional reading.** Equations (10.4.1.10)–(10.4.1.11), pp. 457–458, say the geometric subspace is invariant and distinguish the two noncommuting orders. But the full-space series in (10.4.3.43), p. 472, has every output vector of the form $S_a(\psi)$, where $S_a$ takes values in the spectral subspace by (10.4.1.5) and (10.4.3.41). Its limit is then identified in (10.4.3.45), p. 473, with convolution **after** spectral projection, although the sentence introducing that equation points back to the quotient-space series number (10.4.3.42). The distinction matters also for the companion geometric operator: Definition 10.4.1.5, p. 458, calls for convolution **after** geometric projection, whereas Theorem 12.1.1.3 works in the opposite order.

**Project check.** Write $H=W_I^s(C_F)$, $A=A(\varphi)$, $P=P_a^{\mathrm{spec}}$, and $Q_a:H\to H_{F,a,I}^s$ for the quotient by $(1-P)H$. Let $\bar A$ denote the quotient convolution. Invariance gives $Q_a A=\bar A Q_a$, and $S_a Q_a=P$. If $B_N$ are the finite sums on the quotient in (10.3.2.1), then the displayed full-space sums in (10.4.3.43) are $S_a B_N Q_a$: Their functionals are pulled back by $Q_a$, and their output vectors are lifted by $S_a$. Taking the claimed trace-norm limit of $B_N$ to $\bar A$ yields $S_a\bar A Q_a=PA$, not $AP$ in general. In particular, no limit of these operators can recover the geometric output block $(1-P)AP$.

Since $AP=PA+(1-P)AP$, conditional on the quotient nuclearity in Theorem 10.3.2.1, $AP$ is trace class exactly when $R=(1-P)AP$ is trace class. In that case $R$ has zero trace by its off-diagonal block form, and $\operatorname{Tr}(AP)=\operatorname{Tr}(\bar A)$. This does not say that $R$ has zero diagonal or zero trace after multiplying by a cutoff. For a control take the counting-measure Hilbert space $\mathbb C^2$, $u=(1,1)/\sqrt{2}$, $v=(1,-1)/\sqrt{2}$, $P=uu^*$, $A=vu^*$, and $M=\operatorname{diag}(1,0)$. Then $A$ kills the geometric subspace and $AP=A$, $PA=0$, with $\operatorname{Tr}(AP)=0$ but $\operatorname{Tr}(M AP)=1/2$. This is a counterexample to a formal substitution of orders in a cutoff trace, not a counterexample for the manuscript's idele-class operators.

## What the cutoff limit actually needs

**Conditional project argument for (10.4.2.20).** For the cutoffs of Definition 9.3.3.1, p. 427, $0\le\rho\le1$ and the plateau exhausts each fixed norm under the stated $\varepsilon\Lambda=o(1)$ regime. Thus $M_\rho\to 1$ strongly on the weighted $L^2$ space by dominated convergence. For any trace-class $T$, this implies $\|(M_\rho-1)T\|_1\to0$: On a rank-one term $f\otimes h^*$ the norm is $\|(M_\rho-1)f\|\|h\|$, and finite-rank approximation in trace norm and the uniform multiplier bound pass to $T$. Taking $T=AP$ gives the claimed limit once $AP$ is known to be trace class. The same limit works for a changed lower endpoint if the cutoffs remain uniformly bounded and tend pointwise almost everywhere to 1; this does not control the uncut regular convolution or the local logarithmic integrals. The proof in §12.1.1 already uses the trace-ideal principle for a different strongly convergent family (p. 502, before Theorem 12.1.1.3).

## Why the canonical-lift norm bound fails

**Provisional source reading, independently checked in the PDF extraction.** The proof of Theorem 10.4.2.8 takes $A$ after the lifts, but (10.4.2.23)–(10.4.2.24), p. 463, posit a single bound on the lifted quotient vectors for fixed character and lift tolerance. Proposition 10.2.2.2, (10.2.2.7)–(10.2.2.8), pp. 446–447, instead bounds the coefficient functionals in the reciprocal-weight norm. An upper bound on the functionals is not an upper bound on the vectors biorthogonal to them. Also read the coefficient in (10.4.2.22) as the exponent $b+it$ for a zero at $a+b+it$, as in (10.2.2.4) and (10.4.2.29): In the kernel of $Q_a$ the theta profile is already weighted by $|\cdot|^a$, so the unweighted Mellin evaluation gets its shift from the profile. The calculation below tests this intended system, not the literal extra $a$ in the coefficient display.

**Project counterexample to the uniform upper bound.** Take $F=\mathbb Q$, $a=1/2$, the trivial compact character, and $s>1$. For an on-line simple zero at height $t$ the functional on $H$ is $\ell_t(f)=\int f(g)e^{itx}\,d\mu(g)$, with $x=\log|g|_{\mathbb Q}$. Let $w(x)=e^{2\alpha|x|}(1+x^2)^{s/2}$. The norm of the difference of two such functionals is given by

$$\|\ell_t-\ell_u\|^2=\int |e^{i(t-u)x}-1|^2w(x)^{-1}\,d\mu(g)\longrightarrow0\qquad (t-u\to0).$$

This uses dominated convergence, since the norm-one part has finite Haar measure and $w^{-1}$ is integrable also for $\alpha=0$. Theorem 1 of [Conrey (1989)](https://doi.org/10.1515/crll.1989.399.1), p. 4, with (8) and (11), p. 3, gives $\gg T\log T$ simple critical-line zeros up to $T$. Their ordinates are distinct. If there are $N$ such ordinates in $[0,T]$, the smallest consecutive gap is at most $T/(N-1)$. Hence there are distinct pairs with $|t-u|\to0$. Biorthogonality gives $(\ell_t-\ell_u)(v_t)=1$ for every lift $v_t$ of the quotient vector with label $t$. Thus $\|v_t\|\ge\|\ell_t-\ell_u\|^{-1}$ along these pairs. In particular the canonical lifts do not satisfy (10.4.2.24). This does not estimate $A v_t$ or disprove the claimed trace formula.

**The rank-one estimate does not bypass this issue.** In (10.4.2.26)–(10.4.2.28), p. 464, the correctly modulus-squared integral equals $\|(A v_t)\otimes\ell_t\|_2^2=\|(A v_t)\otimes\ell_t\|_1^2$, not its trace norm. Summing squares does not give the absolute trace-norm summability needed for a rank-one expansion. Haar shearing is valid, but leaves shifted weight ratios and translated-vector correlations; neither can be discarded to extract a Mellin moment as in the passage to (10.4.2.34). On the other hand, Mellin moments do arise by acting on the coefficient functionals by transpose in (10.3.1.10)–(10.3.1.12), pp. 448–449. Arbitrary lifts also cannot identify $AP$: Changing a lift by $z\in(1-P)H$ adds the term $Az\otimes\ell_t$, invisible on the quotient.

**Next operator check.** The [rational singleton repair](trace-spectral-q.md) directly proves $AP\in\mathcal S_1$ and computes its trace in the trivial isotype, without a basis estimate. Its local finite-rank argument does not transfer directly to the positive-width analytic strip. The [positive-width jet-quotient repair](trace-spectral-strip-q.md) instead groups high zeros and proves $AQ$ is trace class, including the off-diagonal block, at almost every width. Here $Q$ is the projection onto the span closure of the zeta jets, which agrees with $P$ only after proving totality on the theta quotient. The cited approximation theorem does not give that identification as extracted. The quotient trace formula is still a separate premise: Even its singleton proof invokes a uniform biorthogonal-vector bound after (10.3.1.18), pp. 451–452, and this note does not audit the positive-width $p=1$ convergence argument in Theorem 10.3.2.1, pp. 454–455. For each fixed smooth cutoff, $M_\rho AP$ is already trace class if $M_\rho A$ is trace class as in Theorem 9.3.3.5(2), pp. 428–429; that does not give uniform trace-norm control as the cutoffs exhaust the group. Merely proving the trace identity for $PA$ does not identify the kernel partitioned in (11.3.1.4), p. 494, or the diagonal used on p. 520.

## From the weighted kernel to the Haar diagonal

**Provisional reading, independently checked in the PDF extraction.** In (9.2.2.34) and (9.2.2.41), p. 417, the two norm exponents are twice the endpoints of $I$, so for $I=[-\alpha,\alpha]$ the weight is $w(g)=\max(|g|_F^{-2\alpha},|g|_F^{2\alpha})(1+|\log|g|_F|^2)^{s/2}$. The endpoints are not the spectral parameter $a$ and the displacement $b$ of a zero. The first kernel in (10.4.3.47), p. 473, divides the named spectral kernel by $w(y)$ to obtain a kernel relative to $w\mu$. That is the correct conversion **if** the named kernel is relative to $\mu$. The second formula adds $\rho(x)$ to the same kernel but assigns it to the geometric rather than spectral operator; multiplication on the output cannot switch the projection. Moreover, (10.4.3.49) defines the named spectral kernel as $k(x,y)/w(y)$ without identifying the raw $k$ in that definition. For consistency with the first formula in (10.4.3.47), that raw $k$ would have to be $w(y)$ times the Haar-relative kernel, not the weighted Hilbert-Schmidt kernel. Do not substitute one formula for the other without resolving that convention.

**Conditional project repair.** Suppose $T=AP$ is trace class and $k_w$ is its Hilbert-Schmidt kernel relative to $w\mu$. The kernel for the same integral operator relative to Haar measure is $K(x,y)=w(y)k_w(x,y)$. Conjugating $T$ by multiplication by $\sqrt w$ gives a trace-class operator on $L^2(C_F,\mu)$ with kernel $h(x,y)=\sqrt{w(x)}k_w(x,y)\sqrt{w(y)}$. These identities hold initially only almost everywhere for the product measure. To reach the diagonal, take normalized averages $B_n$ on $xU_n\times xU_n$ as in Definition 12.1.1.1, pp. 498–499, for a genuine shrinking $D'$-sequence (see below). The singular-value argument below replaces the passage on p. 500 that treats compressions to individual eigenspaces as converging to the whole operator. It also supplies the absolute-average control needed at (12.1.1.13), p. 501.

1. Write the singular-value expansion $h=\sum_j\sigma_j u_j\otimes\overline{v_j}$ in $L^2(\mu\otimes\mu)$, where $\sum_j\sigma_j<\infty$ and the singular vectors have unit $L^2(\mu)$ norm. Use the one-variable averages $A_n$ over $xU_n$ and the estimate $\|Mf\|_2\le C\|f\|_2$ for $Mf=\sup_n A_n|f|$ on a tail with compact closure. The manuscript states a limsup in (A.5.3.16), p. 582; for the supremum used here, the covering lemma (A.5.3.1), p. 579, applies to all translates with averages over the threshold. A disjoint selection on compact truncations gives the global weak $(1,1)$ bound. Splitting $|f|$ at half the threshold and integrating that bound gives the strong $(2,2)$ bound. This bound and density of continuous compactly supported functions in $L^2$ also give one-variable differentiation: It holds for the approximants by shrinking, and the maximal bound and Chebyshev's inequality force the limsup error to vanish almost everywhere.
2. The function $D(x)=\sum_j\sigma_j Mu_j(x) Mv_j(x)$ is integrable by Cauchy–Schwarz and bounds every diagonal average $B_n|h|$, using the product form and local $L^1$ convergence on each averaging box. The analogous bound for a tail of the series tends to zero wherever $D$ is finite. Differentiation in one variable (Theorem A.5.4.1, pp. 582–583) for the countably many singular vectors therefore gives $\widetilde h(x,x)=\sum_j\sigma_j u_j(x)\overline{v_j(x)}$ almost everywhere. Its integral is $\operatorname{Tr}(T)$ by the trace formula for the rank-one terms.
3. For a continuous multiplier $q$ on the product, the discrepancy between $B_n(qh)$ and $q(x,x)B_n h$ is at most the oscillation of $q$ on the averaging box times $D(x)$, which tends to zero. This gives $\widetilde K(x,x)=w(x)\widetilde k_w(x,x)=\widetilde h(x,x)$ almost everywhere. The bound on **absolute normalized** averages is needed here; convergence of signed averages alone does not justify the continuity argument from (A.5.4.16), p. 585. In particular $\int \rho(x)\widetilde K(x,x)\,d\mu(x)=\operatorname{Tr}(M_\rho T)$ for the continuous bounded cutoffs, by the same rank-one trace calculation.

For the repaired Haar-relative geometric kernel $G(x,y)=\varphi(xy^{-1})-K(x,y)$, the first term is continuous and has diagonal value $\varphi(1)$. Hence if $\varphi(1)=0$, $\widetilde G(x,x)=-\widetilde K(x,x)$ is integrable with integral $-\operatorname{Tr}(T)$. For a fixed smooth cutoff with $M_\rho A$ trace class, $M_\rho(A-T)$ is trace class as well, with trace $\int\rho(x)(\varphi(1)-\widetilde K(x,x))\,d\mu(x)$. Neither identity identifies $G$ with the literal kernel of (10.4.3.50) or with the kernel in the geometric calculation.

### The averaging boxes must actually shrink

**Verified source and ordinary-math counterexample on $C_{\mathbb Q(i)}$.**
The previous extraction check only located a missing shrinking hypothesis.
The rendered displays and the two computations below show that the literal
boxes also give a different diagonal integral for a continuous rank-one
kernel. This does not refute Theorem 12.1.1.2 under its stated $D'$ hypothesis.

**Printed route.** The logarithm in §A.5.2.2, p. 574, just below
(A.5.2.9), records $\log|u_v|_v$, not the complex phase. The rendered
(A.5.2.19)–(20), p. 576, give the full inverse image $\mathscr L^{-1}(P_k)$,
with the coefficient indices $1\le i\le r_1+r_2-1$, and no angular
restriction. Thus the general-field Archimedean boxes are invariant
under $\ker\mathscr L$. This is not an angular slice of the fundamental
domain in (A.5.2.7), p. 574. For $F=\mathbb Q(i)$ the defining sum is
empty, so $P_k=\{0\}$ and $U_{S_\infty,k}=S^1$. Equations
(A.5.2.23)–(24), p. 577, give $U_k=\tau(I_k)(S^1\times B_k)$ with
$I_k=(1-1/k,1+1/k)$; take the tail $k\ge2$. Lemma A.5.2.17(1), p. 577, takes the quotient **image**
$\overline U_k=q(U_k)$ in $C_F$, and Definition A.5.2.18(2), p. 578,
designates these images as standard. Here $q$ is the diagonal-principal
quotient and $N(x)=|x|_F$ is the descended norm, as in (A.1.4.1)–(2),
p. 542. The image $H=q(S^1\times\{1\})$ is an embedded circle:
A principal idele equal to $1$ at all finite places comes from $1\in F^\times$.
Every $\overline U_k$ contains and is translation-invariant under $H$,
regardless of the permitted $B_k$ or norm section $\tau$. Indeed,
$S^1\times B_k$ is an open compact subgroup of the norm-one ideles:
Inside the open finite-unit stage, norm one means exactly $|z|=1$ at
infinity. The section splits off $I_k$, whose closure is compact in
$\mathbb R_{>0}$ on this tail, and $q$ is open. The boxes therefore have
positive finite Haar mass, but cannot fit inside an identity neighborhood
missing a fixed nonidentity point of $H$. They fail the shrinking
requirement of Definition A.5.2.1, p. 569, recalled in Definition
12.1.1.1, p. 498.

**Witness and hypotheses.** Write $G=C_{\mathbb Q(i)}$, and let $\mu$ be
Haar measure on $G$. For an idele $a$, the finite fractional ideal with
valuations $v(a_v)$ is principal because $\mathbb Z[i]$ is Euclidean. If
$\alpha$ generates it, then $a/\alpha$ is a representative with every
finite component a unit. Two such representatives of a class differ by a
Gaussian unit, and each Gaussian unit has fourth power $1$. The restriction
of $q$ to the open subgroup $\mathbb C^\times\times\widehat{\mathbb Z[i]}^\times$
is therefore an open surjection with kernel the diagonal Gaussian units.
In this quotient model the formula $\chi([z,u])=(z/|z|)^4$ gives a
continuous unitary character. Its restriction to $H$ sends $\zeta$ to
$\zeta^4$, hence is nontrivial. The quotient model also gives a Hausdorff,
locally compact, second countable abelian group. On its normalized
representatives $N([z,u])=|z|^2$; the complex norm convention is as in
Lemma A.2.2.6, p. 547. In particular the inverse image of a compact
log-norm interval is the image of a compact annulus times the compact
finite unit group. For nonzero $b\in C_c^\infty(\mathbb R)$, both
$f(x)=b(\log N(x))\chi(x)$ and the radial control $f_0(x)=b(\log N(x))$
are nonzero in $C_c(G)$ and have the same absolute value.

**Box average, calculated directly.** Definition 12.1.1.1 and (12.1.1.1),
p. 498, normalize Haar on each translated box; the opening of p. 499
specifies product boxes for a kernel. The same p. 498 names the Appendix A
construction for the idelic groups. Applying the averaging expression
outside its $D'$ hypothesis, set
$A_k g(x)=\mu(\overline U_k)^{-1}\int_{x\overline U_k}g(y)\,d\mu(y)$.
For $h\in H$ with $\chi(h)\ne 1$, translating the integration set by $h$
leaves both the set and Haar measure unchanged, while $f(hy)=\chi(h)f(y)$.
It follows that $A_k f=0$ for every $k\ge2$. By Fubini, the average of
$K(x,y)=f(x)\overline{f(y)}$ on the product is
$A_k f(x)\overline{A_k f(y)}$. Its limit is identically zero, including
on the diagonal, so the left side of (12.1.1.2), p. 499, is zero.
For $f_0$, every $v\in\overline U_k$ has $N(v)\in I_k$, so
$$
 |A_k f_0(x)-f_0(x)|\le
 \sup_{t\in I_k}|b(\log N(x)+\log t)-b(\log N(x))|\longrightarrow 0.
$$
The radial limiting diagonal is $|f_0|^2$ and integrates to its true trace.
The control tests the norm coordinate, not differentiation in the finite
directions. The same cancellation applies to any integrable-on-boxes
function transforming by a nontrivial character of $H$.

**Operator trace, calculated without the boxes.** Take $\lambda=\mu$ in
Theorem 12.1.1.2, p. 499, so the continuous positive density is $1$.
The kernel $K$ is continuous, locally integrable for product Haar measure,
and Hilbert–Schmidt. The integral operator
$Tg=f\int_G\overline f g\,d\lambda$ is positive rank one, hence nuclear,
with sole nonzero eigenvalue $\|f\|_{L^2(\lambda)}^2>0$. This is the trace;
it is the same positive value as the radial trace. The comparison works
also for any measure $\lambda=w\mu$ with continuous strictly positive $w$:
The averaging in the definition still uses Haar measure, and the rank-one
trace changes to the squared norm for $\lambda$, still positive. The kernel
and measure here are for the rank-one test, not an identification of a
spectral or geometric operator in Chapter 12.

**Scope and handoff.** The rank-one mismatch rules out treating the
printed global boxes as general trace-diagonal boxes on the nontrivial
angular isotype. The theorem on p. 499 explicitly assumes a $D'$-sequence,
and no claim about agreement for its actual trace-formula operators or
refutation of Theorem 12.5.1.1 follows. For a bounded next check, pass these
same boxes to $G/H$ and test whether their product averages for an arbitrary
trace-class kernel with a radial positive continuous weight compute the
trace of the angular-invariant compression $P_H T P_H$, where $P_H$ is
normalized circle averaging. That would identify exactly what the literal
procedure measures, before testing the missing trace on the actual
Chapter 12 operators. The weighted-kernel convention and local-to-global
comparison remain separate.

**Review evidence.** Worker session
`01a2024b-f7e1-7425-9679-b5f9d300a2e7` inspected rendered crops of the
box path (pp. 574, 576–578), the class-group and norm conventions
(pp. 542, 547), the shrinking requirement (p. 569), and the averaging
and trace statements (pp. 498–499). The independent dispatch
`angular-review` (`wbutWxa`, Yah session
`01a2024b-f7e1-7425-9679-b5f9d300a2e7`) corroborated the source path by
extraction only, not by viewing the renderings. It separately checked
character descent, cancellation in each Haar average, the radial limit,
and the positive eigenvalue for $\lambda=\mu$. Its identification of
$H$ as a quotient by the Gaussian units is not used: The units are
embedded diagonally and have nontrivial finite entries unless they are
$1$, so the Archimedean-only circle maps injectively. This correction
does not affect the review's transformation law $\chi(q(\zeta,1))=\zeta^4$
or its two numerical conclusions. No claims about other fields or
finite-direction differentiation from the review are needed. This is
ordinary mathematics, not a Lean result.

**Project repair.** Use shrinking symmetric coordinate boxes in the identity component of $F_\infty^\times$ (including complex angular coordinates) times a decreasing compact open subgroup base in the finite ideles. Choose the initial product small enough that the quotient by discrete $F^\times$ is injective on its difference set. The compact open factors do not grow under $U_nU_n^{-1}$, and the real coordinate boxes double in each coordinate. Haar measure on the quotient agrees locally up to scale, so the required volume ratio is bounded. The singular-value formula gives the same trace-class diagonal almost everywhere for any two bases satisfying the shrinking and doubling hypotheses, but not for the literal nonshrinking boxes. The local-to-global comparison must use compatible repaired bases or prove that the difference does not affect its tests.

## Strip endpoints

In (10.3.2.3)–(10.3.2.4), p. 454, the sum includes $b=\pm\alpha$ with capped multiplicities, while the p. 520 target includes only interior zeros with their full orders. At $a=1/2$, the parameter $c=\chi|\cdot|_F^{1/2+b+it}$ gives the Mellin argument $c|\cdot|_F^{-1/2}$ and orders agree for $|b|<\alpha$. They do not therefore agree on the entire sum.

**Conditional project repair.** The countable set of unitary base points in Theorem 10.3.2.1, p. 453, has only countably many zeros across its non-identically-zero meromorphic Hecke functions. The excluded positive widths $\alpha=|\operatorname{Re}(z)-1/2|$ for these zeros form a countable set. If the common geometric evaluation and the downstream application permit widths in a nonempty open interval for the given field, choose one outside this set. This is not permission to change a prescribed strip or claim the equality for every width. If a width is fixed, account for its boundary contribution. Taking $\alpha=0$ in the singleton construction does not prove the interior-strip sum.

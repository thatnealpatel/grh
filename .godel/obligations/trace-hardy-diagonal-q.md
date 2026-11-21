# Direct diagonal of the rational unit-band Hardy model

**Scope:** $F=\mathbb Q$, trivial compact isotype, band $B=1$, Sobolev degree zero,
and $0<\alpha<1/2$. This computes the positive-log **position** cutoff of the
Hardy compression from the [reverse-lift control](trace-reverse-lift-q.md),
without dividing by zeta. It does not compute the manuscript's global $S$
piece. Lean checks the single-vector overlap, its pairing with a causal
convolution profile on a sharp cutoff, and the position limit of that pairing.
The full operator calculation and its cutoff limit below are independently
reviewed mathematics, not Lean results.

## Operator and source match

Write $c=1/2-\alpha$. In the causal log coordinate of the reverse-lift model,
the isometry $h(x)\mapsto e^{\alpha x}h(x)$ gives $H_+=L^2(0,\infty)$
and the Hardy theta subspace $I H_+$, where $I$ is the inner factor of
$W(z)=((z-1)/(z+1))\zeta(z)/(z+1)^2$ in $\Re z>c$. Here multiplication
by $I$ is understood on the Laplace side. Write $Q$ for the orthogonal
projection in $H_+$ onto $I H_+$, and $P_K=1-Q$. For a smooth $f$ compactly
supported in $(0,\log 2)$ (in particular for the mass-zero subfamily), set
$g(y)=e^{\alpha y}f(y)$ and let $C_g$ denote causal convolution. The
operator whose trace is calculated is $M_\rho C_g Q$ on $H_+$, equivalently
the compressed cutoff operator $Q M_\rho C_g|_{I H_+}$. None of these
formulas changes the designated order of cutoff, convolution, and projection.

**Provisional source comparison from the digest-matched layout extraction:**
Definition 10.1.1.1(1), (10.1.1.3), p. 433, takes the global theta closure
in the full weighted space. Definition 10.4.1.3, p. 457, uses the order
$M_\rho P_a^{\mathrm{geom}}A(\phi)$ for geometrically truncated convolution.
Definition 10.4.1.5, (10.4.1.12)–(10.4.1.13), and the kernel discussion at
(10.4.3.48)–(10.4.3.50), pp. 473–474, also treat
$M_\rho A(\phi)P_a^{\mathrm{geom}}$. The two orders should not be identified
at finite cutoff by cycling bounded factors through an unproved trace.
Theorem 11.2.1.4(2), (11.2.1.8)–(11.2.1.10), p. 489, concerns the
**global** Paley–Wiener level limit with position cutoff fixed, for tests
above norm one. Definition 10.4.3.7 assumes $s\ge3$, unlike this model.
Theorem 12.5.1.1, pp. 519–520, uses the positive Mellin exponent $z-1/2$
and zeros **interior to a strip**. Its proof invokes Theorem 12.4.1.1,
pp. 514–519, to identify the global $S$ piece after two Mellin subtractions.
The local formula (12.4.1.25)–(12.4.1.28) instead yields local integrals and
the norm-one logarithmic term. Neither that local formula nor the global
level limit gives a model-space overlap formula or identifies the global
$S$ piece with the compression here. The calculation below is a project
control for the latter compression, not a replacement for that identification.

## One zero and the fixed-cutoff diagonal

For bounded compactly supported $\rho$, choose $R$ with its half-line
support in $[0,R]$. Causality lets us restrict the input of $M_\rho C_g$ to
$[0,R]$. With $\widehat g(t)=\int e^{-ity}g(y)\,dy$, Fourier inversion
expresses the operator as the trace-norm integral of rank-one operators
$$
\frac1{2\pi}\int \widehat g(t)
  \big[h\mapsto\langle h,\mathbf1_{(0,R)}e^{it\cdot}\rangle\rho e^{it\cdot}\big]dt,
$$
where the inner product is linear in the first variable. Each trace norm
before the scalar coefficient is $\sqrt R\,\|\rho\|_2$ and
$\widehat g\in L^1$. Taking traces gives $g(0)\int\rho=0$. This holds
also with $m\rho$ in place of $\rho$ for every bounded multiplier $m$.
Consequently the trace density of $M_\rho C_g Q$ is the negative of the
trace density of $M_\rho C_g P_K$. Here the density is the $L^1$ function
representing $m\mapsto\operatorname{Tr}(M_m T)$ for a trace-class $T$:
Sum the diagonal products of a trace-norm summable rank-one expansion;
Cauchy–Schwarz gives $\|\mathrm{density}(T)\|_1\le\|T\|_1$.

For a single factor at $z_j$, put $a=z_j-c$ and $r=\Re a>0$. The model
space is spanned by the unit vector $u_a(x)=\sqrt{2r}e^{-\bar a x}$ on
$x\ge0$, extended by zero. Thus the negative rank-one diagonal is
$$
  -\rho(x)\,2r\,e^{-2rx}\int_0^x g(y)e^{\bar a y}\,dy,\qquad x\ge0.
$$
The checked proposition `Masullo.halfLineMellinVector_sharpCutoff_overlap`
in `Props.HalfLineMellinDiagonal` supplies the scalar step: For $y\ge0$,
$$
\int_{[0,R]}u_a(x-y)\overline{u_a(x)}\,dx
=\begin{cases}e^{-ay}(1-e^{-2r(R-y)})&y\le R,\\0&y>R.\end{cases}
$$
The proof restricts to the common causal support $[y,R]$, translates its
lower edge to zero, and integrates the decaying exponential. Setting $y=0$
and letting $R$ increase gives the normalization.

### Checked convolution pairing and position limit

In [`Props.HalfLineMellinDiagonal`](../../Proofs/Props/HalfLineMellinDiagonal.lean),
`Masullo.halfLineMellinVector_sharpCutoff_convolution` integrates that
overlap against any $g\in L^1([0,D])$, understood to vanish off $[0,D]$.
Its left side is the actual scalar pairing
$$
J(R)=\int_{[0,R]}\left(\int_{[0,D]}g(y)u_a(x-y)\,dy\right)\overline{u_a(x)}\,dx.
$$
The theorem retains the edge factor and sets the shifted overlap to zero
when $y>R$. To justify Fubini, the vector is strongly measurable and
bounded in modulus by $\sqrt{2r}$ everywhere, so the product integrand is
bounded by $2r|g(y)|$ on the finite-width rectangle.
`Masullo.tendsto_halfLineMellinVector_sharpCutoff_convolution` then gives
$J(R)\to\int_{[0,D]}g(y)e^{-ay}\,dy$ as $R\to+\infty$. For $R\ge D$,
the edge factor lies in $[0,1]$ and tends to one, so the majorant is $|g|$.
Neither scalar theorem needs smoothness or mass zero. In the Hardy chart,
$g(y)=e^{\alpha y}f(y)$, so the limit is $\int f(y)e^{(1/2-z_j)y}\,dy$.
The overlap has the reflected exponent; the separate global minus sign
comes from taking the orthogonal complement. The rank-one projection and
trace-class construction above are not Lean declarations.

## Blaschke exhaustion and then position exhaustion

The inner factor is a pure Blaschke product at the zeros with $\Re z_j>c$,
with multiplicity. Indeed, on each compact zero-free boundary arc $W$
extends across the boundary with modulus bounded below in a small closed
neighborhood. The outer factor and Blaschke factor are bounded, so the
negative log modulus of the singular inner factor is bounded there.
Its Poisson measure on the open arc must then be absolutely continuous,
hence zero. The remaining finite-boundary support is discrete; a mass at
a boundary zero would force exponential decay in the reciprocal normal
distance, inconsistent with the finite order of that zero. A singular
factor at infinity would give exponential decay on the real ray, whereas
$W(x)\sim x^{-2}$. This excludes the singular part.

The finite initial products in Blaschke product order give increasing model
spaces whose projections tend strongly to $P_K$. For instance their
orthogonal complements intersect in $I H_+$: Divide a function in the
intersection by each finite inner product, take a weak limit of these
quotients of equal norm, and use boundedness of point evaluations and
locally uniform product convergence. For fixed $\rho$, trace-class
composition then converges in trace norm by finite-rank approximation;
the diagonals converge in $L^1$. This statement does not assert that the
series of rank-one densities is absolutely summable in $L^1$.

For position exhaustion, use the orthonormal basis $\phi_j=I_{<j}u_{a_j}$
(on the Laplace side), obtained by the orthogonal decomposition for a product
of inner factors. The full-line Fourier modulus of the causal zero extension
is $\sqrt{2r_j}/\sqrt{r_j^2+(t-\gamma_j)^2}$, where
$\gamma_j=\Im z_j$ and $0<r_j=\Re(z_j-c)\le1-c$. For $T=|\gamma_j|\ge2$,
consider $\langle M_\rho C_g\phi_j,\phi_j\rangle$. The part of
$\widehat{C_g\phi_j}$ with $|t|>T/4$ has $L^2$ norm $O_g(T^{-2})$ by
rapid decay of $\widehat g$; the part with $|t|\le T/4$ has $L^1$ and
$L^2$ norms $O_g(T^{-1})$ by the Lorentzian bound. Split the second vector
at $|s|=T/2$, on the full line. The low-band $L^2$ norm is $O(T^{-1/2})$,
so its contribution is $O_g(\|\rho\|_\infty T^{-3/2})$. For the high band
move $\rho$ to the second slot as $\bar\rho$. Its Fourier convolution on
the output low band is bounded pointwise by $O(\operatorname{Var}(\rho)
T^{-1/2})$: Use $|t-s|\ge|s|/2$, the Fourier bound
$|\widehat{\bar\rho}(t-s)|\le\operatorname{Var}(\rho)/|t-s|$, and
Cauchy–Schwarz against the $L^2$ norm of $\widehat\phi_j$. Variation here
is of the zero extension, including the possible jump at zero. The product
formula follows by Schwartz approximation of the high-band vector in $L^2$:
The physical products converge in $L^1$, and the Fourier convolutions
converge uniformly, both by Cauchy–Schwarz. Pairing with the low-band $L^1$
norm now gives the same $T^{-3/2}$ bound times variation. The constants
are uniform in the inner factors and in $r_j$ down to zero.

The zero count $O(T\log(2+T))$ makes that majorant summable by dyadic
blocks. With uniformly bounded compact cutoffs of uniformly bounded
variation that tend to one almost everywhere, the limit can therefore be
taken term by term in the trace. Uncut causal convolution commutes with the
preceding inner-factor isometry, so the $j$-th limiting term is exactly the
one-vector pairing computed above. Hence
$$
\lim_{\rho\to1}\operatorname{Tr}(M_\rho C_g Q)
=-\sum_{\Re z_j>1/2-\alpha}\int_0^\infty f(y)e^{(1/2-z_j)y}\,dy.
$$
This includes sharp $[0,R]$ cutoffs. It is a scalar limit, not an uncut
operator trace or trace-norm convergence. Definition 9.3.3.1, p. 427,
does not impose a uniform variation bound over its prescribed profiles.
Nevertheless, the same Fourier rank-one integral gives a small-transition
comparison in this model. If $d$ is supported in $[b,b+\ell]$ on the half
line, $|d|\le1$, and $\operatorname{supp}g\subset[0,D]$, restrict the input
in that integral to $[b-D,b+\ell]\cap[0,\infty)$. This replaces the uniform
rank-one norm by at most $\sqrt{(D+\ell)\ell}$. For the p. 427 profiles at
large $\Lambda$, the half-line difference from $\mathbf1_{[0,\log\Lambda]}$
is supported in $[\log(\Lambda-\varepsilon),\log\Lambda]$, of length tending
to zero by $\varepsilon<1/\Lambda$. Its trace contribution thus tends to
zero regardless of oscillation in that interval. This is a deduction from
the trace-norm integral, not an additional Lean result. This position result
still does not implement (11.2.1.8)–(11.2.1.10). The half-plane sum includes
zeros at or beyond $1/2+\alpha$; reflection identifies the exponent with
the manuscript's only on reflection-invariant zero families such as the
open strip, not on the full half-plane. No cancellation of those extra
terms or of the two Mellin corrections is proved here.

**Review evidence:** `hardy-review` (`szKmRqB`) checked the fixed-cutoff
model, singular factor exclusion, and source comparison from layout text.
`hardy-limit-review` (`MeeZPoo`) checked trace-class Fourier inversion,
the full-line frequency estimates, and the exact scalar endpoint.
`causal-statement` (`mjfcaeQ`, reviewing the proposed statements from base
`7a245e695d23aae7b37e32fbeb3cc82c6ec147aa`) independently derived the Fubini
identity and limit, checked the sign and exponent, and verified that the
all-real endpoints require set integrals, not oriented intervals. Its
source review distinguishes Definitions 10.4.1.3 and 10.4.1.5 and confirms
which order occurs in (11.2.1.9); none of the reviews establishes a manuscript
level comparison. No visual check is claimed.

**Lean verification:** The Lean changes in `f5ed775e6f8861bc9d13fdc244c4a6449077040c`
passed `lake --wfail build Proofs` and `lake env leanchecker` for
`Lemmas.HalfLineMellinVector` and `Props.HalfLineMellinDiagonal`.
`#check` confirmed the two new public scalar endpoints, and `#print axioms`
reported exactly `propext`, `Classical.choice`, and `Quot.sound` for both
endpoints and the new measurability and norm lemmas.

## Operator order in the unit-band Hardy model

In this paragraph extend $Q$ to the full line by zero on $H_+^\perp$.
For the causal and anticausal projections $P_+,P_-$ and the unitary inner
multiplier $S$ from the reverse-lift model, $Q=SP_+S^*$. Since $S$ commutes
with full-line convolution and $P_-C_gP_+=0$, the difference is
$$D=QC_g-C_gQ=S(P_+C_gP_-)S^*.$$
If $\operatorname{supp}g\subset[0,d]$, the cross block kernel $g(x-y)$ lives
in $[0,d]\times[-d,0]$. Fourier inversion gives a rank-one integral with
input and output vectors the exponentials restricted to the respective
intervals. The trace norm of each rank-one term before its scalar
coefficient is $d$, so $d|\widehat g(t)|/(2\pi)$ is an integrable majorant;
each term has trace zero by disjoint support. Thus $D$ is trace class with
trace zero. Its range lies in $SH_+\subset H_+$; multiplication by $\rho$
preserves $H_+$, so the full-line trace of $M_\rho D$ agrees with the
trace of its restriction to $H_+$ using a basis adapted to the half lines.
Bounded position cutoffs exhausting the causal half-line give
$M_\rho D\to D$ in trace norm by finite-rank approximation. The scalar
trace difference tends to zero, though the operator difference can persist.

At fixed cutoff this trace difference need not vanish. In the single
Blaschke factor model, on $H_+$ write $1-Q=u\otimes u$ for
$u(x)=\sqrt{2r}e^{-rx}$, $r>0$. Choose $\rho=\mathbf1_{[0,R]}$ and a
nonzero smooth $g\ge0$ supported strictly above $R$, with $R<\log 2$ and
$\operatorname{supp}g\subset(0,\log 2)$. Then $M_\rho C_g=0$, whereas
$(1-Q)C_g=(\int g(y)e^{-ry}\,dy)(1-Q)$, so
$$\operatorname{Tr}(M_\rho D)=-(1-e^{-2rR})\int g(y)e^{-ry}\,dy\ne0.$$
This test need not be in the mass-zero subclass. It distinguishes orders
in the one-factor model, not the two weighted manuscript operators.

For orthogonal $Q_n\le Q$ with $Q_n\to Q$ strongly, the fixed-cutoff
operators $M_\rho QC_gQ_n=(M_\rho C_gQ)Q_n$ converge in trace norm to
$M_\rho C_gQ$. Thus the iterated trace in this model can use the preceding
position limit, but this does not identify the actual global levels.

## The fixed-cutoff limit retains a right projection

**Source audit (digest-matched extraction, provisional):** Definition
10.4.1.3 and (10.4.1.6)–(10.4.1.7), p. 457, give $M_\rho PA$; Definition
10.4.1.5 and (10.4.3.48), pp. 458 and 473, instead use $M_\rho AP$.
Here $P$ is the weighted geometric projection and $A=A(\phi)$. Equation
(10.4.1.10) uses invariance of the geometric space, $PAP=AP$, not
commutation. Theorem 11.2.1.2(1), p. 488, states strong convergence of the
absolute level projectors to $P$. Theorem 11.2.1.4(1), p. 489, gives the
same for invariant levels. The extracted (11.2.1.4) and (11.2.1.9) then
claim the nuclear limit of $M_\rho PAQ_n$ is $M_\rho PA$ on the ambient
weighted isotype at each fixed $\rho$. Their dependency Corollary C.3.5.5,
pp. 702–703, requires projections exhausting the identity on the space under
consideration. Proposition C.3.6.5, pp. 705–706, instead permits a proper
strong limit for the self-adjoint right factor and retains it in the target.

The correct ambient limit from the stated strong convergence and localized
nuclearity is $M_\rho PAP=M_\rho AP$ in trace norm, not $M_\rho PA$ unless
$M_\rho PA(1-P)=0$. Indeed let $T=M_\rho PA$; the level sequence is $TQ_n$,
and C.3.6.5 gives $TQ_n\to TP$. The operator discrepancy is already
forced by uniqueness of the strong limit. Working on $PH$ removes the
right factor on inputs but requires output compression to speak of a trace
on $PH$, since multiplication by $\rho$ need not preserve that space.

## Removing the order defect in the weighted rational isotype

**Scope:** $F=\mathbb Q$, trivial compact isotype, $a=1/2$, even degree
$s=2r\ge4$, and the common full-measure set of widths $0<\alpha<1/2$
defined by the [two-sided zero separation](trace-theta-density-q.md#bounds-for-division-by-zeta).
This is the full weighted theta closure in this isotype, not the unit-band
Hardy space and not an assertion at every width. Let $A$ be convolution by
a smooth compactly supported log profile, including the above-one tests in
Theorem 11.2.1.4. Write $P$ for the **geometric** projector and $J=1-P$ for
its complementary projector. In the pinned layout extraction,
(11.2.1.7)–(11.2.1.10) use $W^{s,2}$ without $I$, the polynomial weight of
(9.1.2.3). At positive width the weight is instead (9.2.2.34), p. 417.
The positive-width levels here are constructed in that norm; no transport
of the printed zero-width orthogonal projectors is used.

The [Gaussian-division result](trace-theta-density-q.md#gaussian-division-and-compact-theta-approximation)
identifies the geometric closure with the interior common jet kernel in the
original weighted norm. Thus $J$ is the projection called $Q$ in the
[strip trace-class result](trace-spectral-strip-q.md#convolution-after-projection),
which controls $AJ$, not just $JA$. This distinction is necessary: The
former gives the off-diagonal block $D=PAJ$, whereas the latter alone does
not. Invariance of the geometric closure gives $PAP=AP$. It follows that
$$
PA-AP=PAJ=D,\qquad \operatorname{Tr}(D)=0.
$$
Indeed $D$ is trace class by the ideal property and has zero trace in a
basis adapted to $PH\oplus JH$: It vanishes on $PH$ and maps $JH$ into
$PH$. If the uniformly bounded cutoffs $\rho$ tend to one almost everywhere,
then $M_\rho$ converges strongly to the identity by dominated convergence
in the original weighted norm. C.3.6.5 with $p=1$ (or finite-rank
approximation) gives $M_\rho D\to D$ in trace norm, so
$\operatorname{Tr}(M_\rho PA)-\operatorname{Tr}(M_\rho AP)\to0$.
This is neither an operator equality nor a proof of zero defect at fixed
cutoff in the weighted model.

In this rational isotype the terms in the last difference are defined at
fixed compact position support. The log convolution kernel of $M_\rho A$
uses input on a fixed compact enlargement of that support, where the
weighted and ordinary norms are equivalent. Before multiplying by $\rho$,
smooth convolution restricted there is bounded into every fixed-order
Sobolev space on a larger interval, using a smooth output bump that is one
on the cutoff support. Place the bumped output on a circle containing the
interval. The inclusion of its $H^2$ space in $L^2$ is trace class by the
summable Fourier singular values; multiplication by $\rho$ on that
interval and extension by zero are bounded. This proves localized trace
class for $M_\rho A$ and hence $M_\rho AP$; add $M_\rho D$ to obtain
$M_\rho PA$.

The Lean theorem
[`Masullo.tendsto_rationalThetaWeightedEvenBand_projection`](../../Proofs/Theorems/RationalThetaBandClosure.lean)
checks the strong limit $P_n\to P$ of the increasing cofinal real-band
levels in the weighted even lattice chart. For each fixed compact $\rho$,
C.3.6.5 then gives $M_\rho PA P_n\to M_\rho AP$ in trace norm for those
levels. The term on the right has the terminal projection before using
invariance; exhausting position only *after* this limit makes the scalar
order difference vanish on the common widths above. Neither this argument
nor (11.2.1.9) supplies a bound uniform in two moving cutoffs. The
trace-class steps in this section use the independently reviewed paper
repairs above; they are not Lean declarations.

**Next manuscript test:** Keep the corrected right projection through the
fixed-cutoff global-to-local comparison. On the [positive-log mass-zero
control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control),
identify the integral of the global $S$ component from (11.3.1.4), p. 494,
with the normalized local level of (11.2.1.6), not with the Fourier
multiplier of (12.4.1.8–12), p. 517. Track any correction and test whether
it supplies the remaining $-\widehat f_{\rm M}(1/2)$ after the local
model's $-\widehat f_{\rm M}(-1/2)$ term. The operator-order estimate
above is for the **whole** ambient trace. It cannot be applied separately
to an $S$ piece or shell without identifying that piece and its localized
trace. The p. 520 inference from Theorem 12.4.1.1 after both subtractions
still requires that identification and the orbital accounting. Compare at
the same width and justify any passage from the iterated level-first limit
to a different joint local cutoff; do not infer it from strong convergence.

**Review evidence:** `order-review` (`xbaKdtT`) checked the Hardy
cross-block calculation, fixed-cutoff witness, and the ambient limit
against the pinned layout text; `weighted-level-review` (`AZjIddc`)
independently checked the right factor and scalar defect.
`level-order-statement` (`rtajUvr`, based on `39a6f063c6a73c04d0765c28b0614b1a35eedf80`)
reviewed the strong projection endpoint, the identification $J=Q$ in the
original strip weight, the fixed-cutoff nuclear limit and subsequent
position limit, and the zero-width versus positive-width source notation.
No visual review is claimed.

**Remaining manuscript-facing obligation:** Compare the actual global
level operators of (11.2.1.8)–(11.2.1.10) with an independently evaluated
localized diagonal in the same weighted degree and cutoff order. In
particular, account for the extra half-plane zeros and both Mellin
subtractions before using the model result in (12.5.1.4). The
[above-one geometric control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control)
is an independent test of the missing global $S$-piece identification.

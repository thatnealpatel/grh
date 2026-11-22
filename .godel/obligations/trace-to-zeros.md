# From a trace identity to a statement about Hecke zeros

**Status: Provisional readings from `pdftotext -layout` of the [digest-matched edition](../sources/masullo/README.md), and project reasoning as labeled.** Page numbers are PDF ordinals. This does not extend or replace the [visual finding on pp. 522–523](divisor-heading.json).

## The two trace statements have different interfaces

- **Theorem 12.5.1.1, pp. 519–520:** The test is in $D(C_F)$ and vanishes on $C_F^1$. Equations (12.5.1.1)–(12.5.1.4) use zeros in the interior of a strip with full orders $N(c)$.
- **Theorem 13.3.1.1, p. 522:** The test obeys the Mellin-jet conditions (13.3.1.2), with derivative orders $0$ through $[F:\mathbb Q]-1$. Equations (13.3.1.1) and (13.3.1.3) restrict the spectral sum to the critical line and use $N_{\mathrm{spec}}(c)=\min\{N(c),[F:\mathbb Q]\}$. The heading that follows has an unresolved theorem reference and a footnote asking for the statement. Check the exact test class, weights, and local factors before comparing these statements. The text's description of Chapter 13 as a restatement does not justify specializing the strip, clipping orders, or changing test classes.

**Project control for the test class.** Take $F=\mathbb Q$ and a radial test $\varphi(g)=h(\log|g|_F)$ for a nonzero nonnegative smooth $h$ compactly supported in $(1,2)$. The norm-one subgroup is compact, so the radial lift is a smooth compactly supported test (it factors through the Lie quotient $\mathbb R_{>0}$). It vanishes on $C_F^1$. But the $k=0$, trivial-character condition in (13.3.1.2) integrates it against a positive Haar measure and is not zero. Thus the Chapter 12 condition does not imply the Chapter 13 condition, independently of whether either trace formula holds.

## Two proposed deductions, not two proofs

- **Holomorphic approximation:** §§1.4.2–1.4.6, pp. 28–30, sketch a one-sided family of tests and a Montel/analytic-continuation argument for the finite Hecke logarithmic derivative. Section 1.4.6 and the letter excerpt on p. 35 explicitly say that Weil positivity is not used in this route. The extraction of p. 522 n. 3 also requests a deduction by approximation, but with $e^{-s|\log t|}$, not the one-sided family. The two approximations need separate interfaces.

  **Project control, independently challenged by a Yah text reader.** For $F=\mathbb Q$, trivial $\chi$, and a fixed real $z>\max(1,\sup I)$, take the proposed nonnegative cutoff and mollifier. If the resulting smooth compact profiles $a_n$ are supported above $1$ and converge to $t^{-z}$ for $t>1$ as requested, the two real unit terms on p. 29 add. They give

  $$A_n=\int_1^\infty a_n(t)\frac{t^{-1/2}}{t-1}\,dt.$$

  Fatou's lemma on $(1,2)$ gives $\liminf_n A_n=+\infty$, since $t^{-z-1/2}$ tends to $1$ at the singular endpoint. This is already failure at one parameter, not just a failure of uniformity in $z$. If the Archimedean term is read as a principal value, the individual cutoff tests still have zero value at the singularity, so the supported terms in (B.4.3.13), p. 619, supply no subtraction. Compare (B.4.4.20), p. 625; the divergence in modulus does not depend on an overall sign. This blocks the displayed separate Archimedean bound, not the conclusion about zeros or every continuation argument. The [fixed-parameter subtraction below](#fixed-parameter-subtraction-over-the-rationals) gives a conditional continuation argument over $\mathbb Q$ without a Montel subsequence.
- **Positivity:** §14.1.2, pp. 528–529, describes the intended content of Theorem 13.3.1.2 as location on the critical line and a degree bound away from the central zero, with a caveat on the parametrization of the central point. It credits a positivity criterion with an unresolved theorem reference; see also p. 533. This is evidence of the author's intended result, not a statement or proof printed under the heading on p. 522. Proposition 14.1.2.3 on p. 531 assumes separate conjectures and cannot supply an unconditional deduction. A positivity repair would need a precise criterion applicable to the available test class, with enough tests to detect off-line zeros and distinguish clipped orders from true orders away from the center. The usual nonzero convolution squares cannot be inserted into Chapter 12: For $\psi^*(g)=\overline{\psi(g^{-1})}$, $(\psi*\psi^*)(1)=\int|\psi(g)|^2\,d\mu(g)>0$ for nonzero $\psi\in D(C_F)$. This does not rule out a restricted-test criterion for Chapter 13. A separate [project repair using moment uniqueness](trace-divisor-uniqueness.md) does not require positivity: If the capped and full-order sums agree on the common rational radial tests, the tests detect every noncentral zero and its order. The [real-place normalization test](trace-divisor-uniqueness.md#a-pole-test-for-the-raw-haar-reading) shows why that agreement cannot be read directly from the extracted formulas.

## Full versus positive-width sums on the same tests

**Source interface: Provisional, independently checked against the digest-matched
layout extraction.** Use the trivial compact isotype over $\mathbb Q$, with
$\varphi(g)=f(\log|g|)$ and $f\in C_c^\infty((0,\infty))$. This factors through
the Lie norm quotient; compactness of the norm kernel gives compact support
upstairs. Nontrivial compact characters integrate to zero against the radial
lift, by Haar invariance as on p. 625. The global factor
$\mu_1(C_{\mathbb Q}^1)^{-1}$ in (B.4.4.16), p. 623, is one by (A.3.2.1),
p. 560, so the normalized explicit formula and the raw global trace transform
use the same $dx$ in log norm. The local terms also match *as displayed*:

- The real coefficient is $1/2$ times the two-sign $dt/|t|$ measure,
  as in (B.4.4.4), p. 620, and (12.5.1.1), p. 519. With
  $t=\pm e^x$ this gives the $H(x)$ below; it does not give the two terms
  with identical denominators in §1.4.3, p. 29. Use (12.4.1.1), not the
  adjacent prose on p. 514 that calls the unscaled real $\mu_v$ canonical.
- Finite-place unit-volume factors cancel shell by shell, giving
  $(\log p)p^{-k/2}$ at $x=k\log p$ for $k>0$. Because these tests vanish
  near norm one, no local principal-value subtraction or identity-supported
  correction contributes; compare (B.4.3.13), p. 619, (B.4.4.5), p. 620,
  and (B.4.4.20–22), p. 625. There are only finitely many nonzero prime terms
  for each support band. Both formulas use polar terms at $\pm1/2$.
- Read the full zero sum by order, as explicitly specified before
  (B.4.2.2), p. 614. The set-indexed display (B.4.4.16) lacks a written
  order factor, and the discreteness assertion in its convergence proof
  has a growth caveat (pp. 624–625, nn. 25–26). The Lean quadratic
  summability estimate supplies absolute convergence with the orders over
  $\mathbb Q$, not the explicit formula itself.

Use $\alpha$ for the half-width, not the center $a=1/2$ of §12.5. Whereas
(12.5.1.3–4) states an interior sum, its cited Theorem 10.4.2.8, p. 463,
takes the position cutoff limit at *fixed* $I=[-\alpha,\alpha]$ and invokes
(10.3.2.3–4), p. 454. The latter includes both boundaries with Sobolev-capped
orders. For location, either variant is enough if it is proved: Use any
integer weights $0\le m_\alpha(\rho)\le\operatorname{ord}(\rho)$ supported in
$|\Re(\rho-1/2)|\le\alpha$. Countability permits arbitrarily small widths
without boundary zeros, but does not give arbitrarily small widths at which
all geometric and spectral hypotheses hold. In particular, §1.4, p. 27,
announces arbitrary positive widths with $s=0$, while Definition 10.4.3.7,
p. 473, requires $s\ge3$, and (10.3.2.3) is stated for $s>1$. Use a fixed
permitted degree and establish the two evaluations at the same widths,
not a passage to zero width of the kernel. The [rational spectral repairs](trace-theta-density-q.md) share a full-measure set in $(0,1/2)$, using quantitative separation from the boundary. This is sufficient on the spectral side of that model, not a proof that the geometry works on those widths.

**Checked Lean implication, not a trace formula.** In
[`Props/ZetaTestSumComparison`](../../Proofs/Props/ZetaTestSumComparison.lean),
`Masullo.ZetaStripTestAgreement α` is the exact remaining location premise
at one width: The full and $m_\alpha$-weighted sums agree on all the above
profiles of integral zero. Both sums are absolutely convergent. Subtracting
and applying `weight_eq_zero_of_zero_mass_annihilation` recovers the full
order at each noncentral zero, so every zero outside the closed strip would
retain a nonzero coefficient. `Masullo.zetaZero_in_closedStrip_of_test_agreement`
rules that out. `Masullo.riemannHypothesis_of_strip_test_agreement` proves
Mathlib's `RiemannHypothesis` if this agreement holds for some $0<\alpha<\epsilon$
for each $\epsilon>0$. Mathlib handles the zeros outside the open critical
strip. This does not require a boundary weight formula, a singleton cap, or
agreement at $\alpha=0$. The capped-order conclusion on the separate Chapter
13 test class has not gained its missing equality. Independent Yah review
checked the location interface and width quantifier; Lake, kernel replay, and
axiom checks of the declarations are part of the candidate check.

### First unmatched geometric evaluation and a positive-log control

To prove the agreement using §12.5, the spectral complement from
(10.4.3.50) must be evaluated on the **same** integrated global diagonal as
the shell split. On these tests the convolution kernel's diagonal term
$\varphi(1)$ vanishes, so after the spectral cutoff limit the global
geometric diagonal must give $-\sum_\rho m_\alpha(\rho)\widehat f_\mathrm{M}(\rho-1/2)$,
where $\widehat f_\mathrm{M}(w)=\int_{x>0}e^{wx}f(x)\,dx$. Even granting that
spectral evaluation, (12.4.1.8–12), p. 517, computes the $S$-local raw
Fourier-multiplier diagonal. It does not identify the $S$ summand of the
actual global diagonal in (11.3.1.4), p. 494. In particular, p. 520 invokes
Theorem 12.4.1.1 to make this identification **after subtracting** the two
polar terms, but neither the local statement (12.4.1.1–3) nor its limit
calculation (12.4.1.23–28) contains those subtractions. Section 12.3 on
p. 514, titled “global to S-local deconstruction,” is a placeholder in
the pinned extraction. The first unproved
geometric equality needed by this comparison is the global $S$-piece
identification with that normalized local finite part *minus* both Mellin
moments, with the same cutoff order and a justified vanishing orbital tail.
The [rational radial idelic explicit formula](rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula)
now supplies the scalar comparison on this test class, with both poles,
full zero orders, normalized local pairings, and actual quotient Haar.
It does not identify a trace operator. The remaining global comparison
is not an assumption about zero location.

**Runnable next check:** Take $S=\{\infty\}$, $0<\alpha<1/2$, and degree
$s=2r\ge4$. Choose a nonzero nonnegative bump $b\in C_c^\infty((0,\log 2))$
and put $f=b'$. Then $\int f=0$ but
$\widehat f_\mathrm{M}(1/2)=-\tfrac12\int e^{x/2}b(x)\,dx\ne0$. Choose
$T<2$ above the norm support so the omitted finite-place *linear* terms
vanish. For the specific joint cutoff family of the
[real-place calculation](trace-joint-local-q.md#above-norm-one-the-defect-is-a-single-mellin-moment),
the normalized raw multiplier gives $J_f=\int Hf$, and the actual
**local model** projection gives $J_f-\widehat f_\mathrm{M}(-1/2)$.
The geometric equality required by p. 520 instead gives
$J_f-\widehat f_\mathrm{M}(-1/2)-\widehat f_\mathrm{M}(1/2)$, if the orbital
terms vanish as claimed. Thus for this control a proposed global-to-local
bridge must account for the remaining $-\widehat f_\mathrm{M}(1/2)$.
Compare the traced global $S$-piece from (11.3.1.4) to the actual local
level from (11.2.1.6), not just to its multiplier. Work at fixed cutoffs
first, then justify the limit order in the bridge. In particular, shell
support for the linear local distribution is not a proof of the orbital
trace identification in (11.3.2.1). This is a falsification test for an
uncorrected identification, not a disproof of the global trace or a test
class sufficient by itself for uniqueness.

The [fixed-band transport control](trace-level-transport-q.md) audits the
topology of one possible bridge: Matching uncut local and global generators
does not extend to a bounded injection of positive-width Hilbert levels,
even for this rational band. The same pairing after compact convolution
and fixed position truncation does give a nuclear forward leg. The
[Poisson edge](trace-level-transport-q.md#the-poisson-edge-separates-the-cutoff-traces)
shows that two moving lower cutoffs at scale $1/B$ can keep the local
traces uniformly separated with identical global compressions in that
model. For an overlapping position window, the [unit-band, degree-zero reverse
lift criterion](trace-reverse-lift-q.md) now makes the obstruction exact:
Lifting all compressed outputs in this model requires a weighted
reciprocal-zeta integral. No unconditional bound or identification of
the Mellin terms follows. The quotient projection can instead be used
directly without dividing by zeta. The [weighted prime-carving audit](trace-carving-weight-q.md)
now rules out another direct replacement: At positive width the uncut
finite carvings are invertible on the geometric closure, and their
orthogonal projectors cannot approximate the local projected operator on
a fixed annulus in the common weighted chart. This is a vector-level
obstruction. The [scalar comparison in a specified rational lift](trace-carving-weight-q.md#next-comparison-and-checks)
remains distinct from the identification of the source indentation and
orbital trace.

## Fixed-parameter subtraction over the rationals

**Source comparison (provisional, independently checked in Yah against the digest-matched extraction).** The positive-log radial specialization of the displayed local integral in (12.5.1.1), p. 519, uses $g_\infty=\pm e^x$ with $dx$ on each sign. Its kernel is

$$H(x)=\tfrac12 e^{x/2}\left((e^x-1)^{-1}+(e^x+1)^{-1}\right)=\frac{e^{3x/2}}{e^{2x}-1}.$$

The real terms as written in §§1.4.1 and 1.4.3, pp. 28–29, instead use $|1-t|$ for both signs. Both expressions have the same orders at zero and infinity, so the discrepancy does not affect the subtraction estimate. On $p^{-m}\mathbb Z_p^\times$, both $|g_p|_p$ and $|1-g_p|_p$ equal $p^m$ for $m>0$. The shell has the same multiplicative volume as $\mathbb Z_p^\times$, so the volume cancels in (12.5.1.2) and the coefficient is $(\log p)p^{-m/2}$. The norm-one volume is one over $\mathbb Q$ under (A.3.2.1), p. 560. The polar terms, orders, and shift by $1/2$ are as in (12.5.1.3)–(12.5.1.4), pp. 519–520, with the stated spectral sum over the interior strip. These are checks of the displayed interface, not of the trace proof or the validity of all cited principal-value identities.

**Project repair, conditional on the trace.** Work over $\mathbb Q$ with the trivial character and $x=\log |g|_{\mathbb Q}$. Fix a width $0<a<1/2$. For $f\in C_c^\infty((0,\infty))$, extend by zero to $\mathbb R$ and use $\varphi(g)=f(x)$. The test is smooth because it factors through the Lie norm quotient and has compact support because the norm kernel is compact. It vanishes near norm one, and compact averaging kills the nontrivial character terms. Assume the following rational, one-sided trace identity for these tests:

$$
\int_0^\infty H(x) f(x)\,dx
+\sum_{p,m\ge1}(\log p)p^{-m/2} f(m\log p)
=\int_0^\infty (e^{x/2}+e^{-x/2})f(x)\,dx
-\sum_{w\in Z_a} m(w)\int_0^\infty e^{wx}f(x)\,dx.
$$

Here $p$ runs over primes, $Z_a$ consists of the shifted nontrivial zeta zeros $w=\rho-1/2$ with $|\Re w|<a$, and $m(w)$ is the order of the zero. Only the bounds $H(x)=O(x^{-1})$ near zero and $H(x)=O(e^{-x/2})$ at infinity, with local integrability for $x>0$, are used. The normalization in this interface is raw global Haar with norm-one volume one. This is an input, not a proof of either trace evaluation or of the range of widths for which it holds. In particular, the input is not the classical explicit formula with a sum over **all** zeros. The proof also allows boundary terms with weights bounded by the zero orders: Their shifted real parts still lie in $[-a,a]$, so the same bounds below apply. This does not establish which spectral sum the actual cutoff gives. The construction invoked on p. 520 uses positive Sobolev degree; (10.3.2.3)–(10.3.2.4), p. 454, allow clipped contributions at the boundary. A trace premise must state which terms it includes.

**Admissible tests and uniform bounds.** Fix real $z_0>1$. Take smooth cutoffs $0\le\chi,\psi\le1$ with $\chi(y)=0$ for $y\le1$, $\chi(y)=1$ for $y\ge2$, $\psi(y)=1$ for $y\le1$, and $\psi(y)=0$ for $y\ge2$. For integers $n\ge2$ use

$$f_{n,z}(x)=\chi(nx)\psi(x/n)(e^{-zx}-e^{-z_0x}),\qquad x>0.$$

Each test vanishes near norm one, and no mollification is needed. Let $K$ be a compact subset of $D_a=\{z:\Re z>a\}$. Uniformly on $K$, the uncut difference is $O_K(x)$ at zero, so the Archimedean integrand is bounded there. At infinity the kernel and both exponentials decay. Dominated convergence gives a locally uniform limit $A(z)$ of the Archimedean term, holomorphic on $D_a$.

For the spectral term, put $u_{n,z,\sigma}(x)=e^{\sigma x}f_{n,z}(x)$ with $\sigma\in[-a,a]$. Before cutoff the weighted difference is $O_K(x)$ at zero, its first two derivatives are bounded there, and it and its derivatives decay at least as fast as $e^{-\delta x}$ at infinity, where $\delta=\min(\inf_{z\in K}\Re z,z_0)-a>0$. Both $\|u_{n,z,\sigma}\|_1$ and $\|u_{n,z,\sigma}''\|_1$ are bounded uniformly in $n$, $z\in K$, and $\sigma$. In differentiating the lower cutoff twice, the worst terms have size $O_K(n^2 x+n)$ on $[1/n,2/n]$, with bounded integral. Upper cutoff derivatives contribute bounded integrals by exponential decay. Twice integrating by parts in $e^{i\gamma x}$, without boundary terms, gives

$$\left|\int_0^\infty e^{(\sigma+i\gamma)x} f_{n,z}(x)\,dx\right|\le \frac{C_K}{1+|\gamma|^2}.$$

The classical zeta zero count with multiplicities, $N(T)=O(T\log T)$ for $|\Im\rho|\le T$ (compare the bound per unit ordinate window on p. 642), makes this majorant summable over $Z_a$ with weights $m(w)$ (use dyadic ordinate bands). Each integral tends locally uniformly to $(z-w)^{-1}-(z_0-w)^{-1}$ by dominated convergence for that $w$. Hence the cutoff spectral sums converge locally uniformly to the holomorphic function

$$S_a(z)=\sum_{w\in Z_a}m(w)\left(\frac1{z-w}-\frac1{z_0-w}\right),\qquad z\in D_a.$$

The same subtraction that removes the Archimedean divergence thus provides summable spectral bounds. No assertion about conditional convergence of an unsubtracted zero series is needed.

**What can be recovered.** On $\Re z>1/2$, the ordinary Euler series and dominated convergence give the prime term limit $-F(z)+F(z_0)$, where $F(z)=\zeta'(z+1/2)/\zeta(z+1/2)$. The polar integrals there give $b(z)-b(z_0)$ for $b(z)=(z-1/2)^{-1}+(z+1/2)^{-1}$. These two limits are not asserted on all of $D_a$. Substituting on the common half-plane gives

$$F(z)+b(z)=A(z)+S_a(z)+F(z_0)+b(z_0).$$

Meromorphic identity extends this equality to $D_a$. The plus sign on the left uses the positive prime weights, whose Euler series is the **negative** logarithmic derivative, unlike the sign of the limit as written in §1.4.4, p. 29 (compare (B.6.1.12), p. 638). It also gives the cancellation of the residue $-1$ at the zeta pole. Subtraction at $z_0$ changes only a constant, so it cannot hide any pole of $F$ at a zeta zero. Since $A+S_a$ is holomorphic, there is no nontrivial zero with $\Re\rho>1/2+a$, or, by the functional equation, with $\Re\rho<1/2-a$. This is a fixed-width conclusion, not exclusion at the boundaries. Only if the trace input holds for widths tending to zero does this imply RH. It yields no bound on multiplicities on the critical line and does not use or supply the missing Chapter 13 theorem.

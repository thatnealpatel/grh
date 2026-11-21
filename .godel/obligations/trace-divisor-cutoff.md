# From the zero-mean tests to a subtracted resolvent

**Status: Checked Lean cutoff step.** This is the $D=1$ cutoff step of the [Chapter 13 uniqueness repair](trace-divisor-uniqueness.md#a-one-sided-moment-uniqueness-lemma). The output feeds the [subtracted-resolvent lemma](trace-divisor-resolvent.md). No part of this argument identifies the capped trace with the classical explicit distribution. The [pointwise](trace-divisor-cutoff-pointwise.md) and [integration](trace-divisor-cutoff-integral.md) estimates are checked Lean endpoints. Their [smooth profile specialization](trace-divisor-cutoff-profiles.md) is also in Lean. The scalar and mass limits are in the same module. [CutoffSeries.lean](../../Proofs/Lemmas/CutoffSeries.lean) proves the mass-corrected series identity.

The provisional extraction of (13.3.1.2), p. 522 of the [pinned edition](../sources/masullo/README.md), gives only $k=0$ over $\mathbb Q$. For the trivial compact isotype the norm-section character cancels at the specified parameter, so the condition on the log test is zero integral. The radial measure is $dt/t=dx$ with compact volume one, by Definition A.3.2.1 and (A.3.2.1), pp. 559–560. The capped sum (13.3.1.3) and the full multiplicities specified near (B.4.2.2), p. 614, give the two distributions to compare. Their equality on this test class is a **premise**, not a conclusion transferred from the manuscript. The raw-Haar issue in (13.3.1.4) remains as described in the [pole test](trace-divisor-uniqueness.md#a-pole-test-for-the-raw-haar-reading).

## Statement for formalization

Let $\mu$ be `volume.restrict (Set.Ioi (0 : ℝ))`. Take tests on all of $\mathbb R$ with `ContDiff ℝ ∞`, `HasCompactSupport`, and `tsupport f ⊆ Set.Ioi 0`; in particular they vanish on a neighborhood of zero. Put

$$M(f)=\int f\,d\mu,\qquad T_w(f)=\int e^{wx}f(x)\,d\mu,\qquad \mathcal D(f)=\sum_i d_i T_{w_i}(f).$$

Use an index type $\iota$, $w,d:\iota\to\mathbb C$, $a\ge0$, $\Re w_i\le a$, and `Summable (fun i ↦ ‖d i‖ / (1 + ‖w i‖ ^ 2))`. This stage needs no lower strip bound, countability instance, or separation of poles. Assume $\mathcal D(f)=0$ on zero-mean tests. If given only for real-valued tests (cast to complex), first establish absolute summability for all tests and extend by real and imaginary parts. Fix a real test $h$ of mass one and real $z_0>a$. For $\Re z>a$, prove absolute summability and the `HasSum` identity

$$\sum_i d_i\big((z-w_i)^{-1}-(z_0-w_i)^{-1}\big)=(z^{-1}-z_0^{-1})\mathcal D(h).$$

The moment correction on the right is not generally zero. Keep the subtraction inside the summand. All displayed denominators are nonzero in the indicated half-plane. Rewrite each summand as `Masullo.subtractedResolventTerm`, and take $G(z)=(z^{-1}-z_0^{-1})\mathcal D(h)$ in the residue lemma. The half-plane is a neighborhood of each of its points. For the zeta application, weighted summability is a separate zero-count obligation.

## Implementation order at the pinned Mathlib revision

1. **Compact-test estimate ([Lean endpoints](trace-divisor-compact-test.md)).** Two integrations by parts give $T_w(f'')=w^2T_w(f)$. Hence
   $$ (1+\|w\|^2)\,\|T_w(f)\|\le\int e^{ax}(\|f(x)\|+\|f''(x)\|)\,d\mu.$$
   Use `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` (`MeasureTheory/Integral/IntegralEqImproper.lean`), valid for $\mathbb C$ as a normed real algebra. The boundary products vanish by support, even at $0^+$; the integrands have compact support. Use `HasCompactSupport.deriv` and `tsupport_deriv_subset` (`Analysis/Calculus/Deriv/Support.lean`), `HasDerivAt.cexp`, `Complex.norm_exp`, and `MeasureTheory.norm_integral_le_integral_norm`. This avoids division by $w$, even at $w=0$. `Summable.of_norm_bounded` gives absolute convergence on all tests without any moment condition.
2. **Bound the approximants and take scalar limits (checked).** The [pointwise cutoff lemma](trace-divisor-cutoff-pointwise.md) assumes the profile-bound hypotheses and concludes the two-scale pointwise majorant below. The [integration lemma](trace-divisor-cutoff-integral.md) assumes that majorant, together with continuity and support, and concludes the uniform integral bound. The [smooth profile specialization](trace-divisor-cutoff-profiles.md) instantiates both helpers for the actual `smoothTransition`/exponential profiles and supplies $C_c^\infty$ tests with support strictly above zero. For each $x>0$ both cutoffs are eventually one. The [scalar and mass limits](trace-divisor-cutoff-profiles.md#lean-interface) use `MeasureTheory.tendsto_integral_of_dominated_convergence` with $2e^{-\delta x}$ to pass to the scalar transforms and mass. `integrableOn_exp_mul_Ioi`, `integrableOn_exp_mul_complex_Ioi`, and `integral_exp_mul_complex_Ioi` (`Analysis/SpecialFunctions/ImproperIntegrals.lean`) supply integrability and evaluate the scalar Laplace terms separately.
3. **Correct the mass and pass to the series limit (checked).** Construct $h$ using `ContDiffBump.integral_normed`, `contDiff_normed`, and `tsupport_normed_eq` with a closed support ball strictly above zero. Annihilation applied to $f_n-M(f_n)h$ gives $\mathcal D(f_n)=M(f_n)\mathcal D(h)$. Apply `tendsto_tsum_of_dominated_convergence` (`Analysis/Normed/Group/Tannery.lean`) with majorant $C\|d_i\|/(1+\|w_i\|^2)$. This API requires an eventual bound uniform over **all** $i$, which step 2 supplies through step 1. The limit inherits the bound, giving absolute summability, and uniqueness of limits gives the displayed `HasSum` identity.

A separate Yah reader checked the source interface against digest-matched text extraction and the APIs against Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. No visual reading was performed. The compact-test estimate in step 1 is in Lean. The [integral lemma](trace-divisor-cutoff-integral.md) converts the pointwise majorant below into the sum bound needed by that estimate. The [profile specialization](trace-divisor-cutoff-profiles.md) discharges the profile hypotheses of both helpers and leaves the scalar-limit/series assembly separate.

## Uniform weighted bounds for the cutoff family

**Estimate formalized in the smooth profile specialization.** Let $N=n+2$ for $n\in\mathbb N$, and put

$$
\chi(t)=\operatorname{smoothTransition}(t-1),\qquad
L(x)=\chi(Nx),\qquad U(x)=1-\chi(x/N),\qquad
f_n(x)=L(x)U(x)\Delta(x),\qquad \Delta(x)=e^{-zx}-e^{-z_0x}.
$$

The test is smooth on all of $\mathbb R$ and supported in $[1/N,2N]\subset (0,\infty)$. Both profiles are in $[0,1]$. The first two derivatives of $\chi$ vanish outside $[1,2]$, since it is locally constant there. Choose nonnegative bounds $M_j$ for $|\chi^{(j)}|$ on this compact interval, for $j=1,2$. The chain rule gives the global bounds

$$
|L^{(j)}(x)|\le N^j M_j\,\mathbf 1_{I_N}(x),\qquad
|U^{(j)}(x)|\le N^{-j} M_j\,\mathbf 1_{[N,2N]}(x),\qquad
I_N=[1/N,2/N].
$$

Since $N\ge 2$, the two intervals are disjoint and $L'U'=0$ everywhere. Define $\delta=\min(\Re z,z_0)-a>0$, $A_j=|z|^j+|z_0|^j$ for $j=0,1,2$, and $B=|z-a|+|z_0-a|$. The real-variable complex derivatives give $e^{ax}|\Delta^{(j)}(x)|\le A_j e^{-\delta x}$ for $x\ge0$. Also $H(x)=e^{ax}\Delta(x)=e^{-(z-a)x}-e^{-(z_0-a)x}$ has $H(0)=0$ and $|H'(x)|\le B$ on $[0,\infty)$. Applying the norm mean-value inequality to $H$ on $[0,x]$ yields $e^{ax}|\Delta(x)|\le Bx$. The weighted form matters: It follows by bounding $H'$ directly, not by multiplying an unweighted linear bound by $e^{ax}$.

Use

$$
f_n''=LU\Delta''+2(L'U+LU')\Delta'+(L''U+LU'')\Delta.
$$

For $x>0$, the terms without differentiated $L$ cost at most $(A_0+A_2+2M_1A_1+M_2 A_0)e^{-\delta x}$, including $f_n$ itself. On $I_N$, the $2L'U\Delta'$ term costs at most $2NM_1 A_1$, since $e^{-\delta x}\le1$, and $L''U\Delta$ costs at most $N^2M_2 Bx\le 2NM_2 B$. Both terms vanish off $I_N$. Thus

$$
e^{ax}\big(|f_n(x)|+|f_n''(x)|\big)
\le (A_0+A_2+2M_1 A_1+M_2 A_0)e^{-\delta x}
     +(2M_1 A_1+2M_2 B)N\,\mathbf 1_{I_N}(x).
$$

Integrate on $x>0$. The two positive majorants are integrable there, and the integrals of $e^{-\delta x}$ and $N\mathbf 1_{I_N}$ are $1/\delta$ and $1$, respectively. This yields the required constant independent of $n$ and the spectral index:

$$
C=\frac{A_0+A_2+2M_1 A_1+M_2 A_0}{\delta}+2M_1 A_1+2M_2 B.
$$

The boundary-layer majorant depends on $n$; it is **not** an integrable dominating function for scalar dominated convergence. For each fixed $w$ with $\Re w\le a$, use only $|L U|\le1$ and the bound for $\Delta$ to dominate $e^{wx}f_n$ by $2e^{-\delta x}$. Use the same bound with $w=0$ for the masses. The integrated constant $C$, via the compact-test estimate, is what gives the single summable majorant $C|d_i|/(1+|w_i|^2)$ for the series step.

**Lean split.** The [pointwise cutoff lemma](trace-divisor-cutoff-pointwise.md) takes the profile bounds as hypotheses. The [specialization](trace-divisor-cutoff-profiles.md) supplies them using `Real.smoothTransition.contDiff`, `contDiff_infty_iff_deriv`, and compactness of `Set.Icc 1 2`. `Set.EqOn.deriv` on each open exterior half-line gives the two derivative support bounds, and `HasDerivAt.smul` handles the real cutoffs acting on the complex test. The specialization, unlike the C² pointwise helper alone, supplies admissible $C_c^\infty$ tests before the mass correction. The [integration lemma](trace-divisor-cutoff-integral.md) assumes the displayed pointwise bound, together with continuity and compact support, and concludes the uniform bound by computing the two majorant integrals. The two abstract estimates, the profile specialization, scalar convergence, and the series step with its mass correction are in Lean. Equality of the full and capped distributions remains an explicit premise.

An independent Yah review checked the differentiated expression, support separation, weighted mean-value estimate, and pinned APIs. It also noted that a reusable $C^2$ pointwise helper is not itself a source of admissible $C_c^\infty$ tests: At the annihilation step use the smooth exponential specialization.

## Lean endpoint and next check

`Masullo.hasSum_subtractedReciprocals_of_annihilation` constructs a fixed
normalized real smooth bump (cast to complex) with support in $[1,3]$. The
public endpoint returns one coefficient $c=\mathcal D(h)$ for all $\Re z>a$,
with absolute summability and `HasSum` for the subtracted series. Annihilation
is used only on the corrected tests, after verifying their support and zero
mass. A bound on the original cutoff summands and Tannery's theorem justify
the limit; the same bound passes to the limiting summands. Independent Yah
statement review confirmed the sign, common half-plane, independence of the
coefficient, and explicit status of the annihilation premise. Release checks:
`lake --wfail build Proofs`, `lake env leanchecker Lemmas.CutoffSeries`, and
`#check` and `#print axioms` for the public endpoint.

**Next:** [Assemble the conditional uniqueness proposition](trace-divisor-resolvent.md#next-runnable-step-assemble-the-conditional-uniqueness-proposition).
Use the open half-plane to give eventual equality at the anchor and rewrite
each reciprocal difference to the single subtracted term before summing. The
rational full-versus-capped comparison and its normalization are still open.

# Recovering the divisor from the Chapter 13 test class

**Status:** Conditional project argument over $\mathbb Q$ in the trivial compact isotype. The [assembled $D=1$ uniqueness proposition](../../Proofs/Props/ZeroMassUniqueness.lean) and the [geometric inputs for the shifted zeta family](../../Proofs/Lemmas/ShiftedZetaZeros.lean) are in Lean. [Quadratic summability of the full multiplicities](../../Proofs/Lemmas/ZetaZeroSummability.lean) is in Lean. The [conditional zeta specialization](../../Proofs/Props/ZetaTestSumComparison.lean) is in Lean, but the full-versus-capped comparison is not. Source readings below are provisional unless linked to rendered review; the provisional ones use raw and layout text from the [digest-matched edition](../sources/masullo/README.md). This fills a downstream implication under a specified normalization; it does not supply the Chapter 13 trace or the manuscript's missing positivity criterion.

## The common test class and the missing comparison

Use $x=\log |g|_{\mathbb Q}$ and the radial test $\varphi(g)=f(x)$, where $f\in C_c^\infty((0,\infty))$ is extended by zero. The compact norm-one group has volume one by (A.3.2.1), p. 560. The inner character average in (13.3.1.2), p. 522, vanishes for nontrivial compact characters. For a character trivial on the compact subgroup, the factor $t^{ix_0(\chi)}$ is cancelled by the indicated value of $s$, and the only condition over $\mathbb Q$ is $\int f(x)\,dx=0$. These tests also vanish near the norm-one subgroup. Thus no prescription for the local distribution at the identity affects this comparison. The [rendered moment-domain audit](trace-moment-codimension-q.md) verifies this radial reduction and shows why one scalar correction does not extend to the full test space.

Equation (13.3.1.3) uses a sum over critical-line zeros with weights capped at one in this isotype. In contrast, the classical explicit formula has the full zero divisor. The prose at (B.4.2.2), p. 614, specifies that its zeros are counted with multiplicity; the idelic display (B.4.4.16), p. 623, does not write a separate order factor. In the latter display the spectral and polar factors $1/\mu^1(C_F^1)$ are one over $\mathbb Q$, and the finite unit volumes are one by (A.3.2.2), p. 560. But the real-place integral has the prefactor $1/M_v=1/2$, also present in (12.5.1.1), p. 519. Equation (B.4.4.4), p. 620, distinguishes canonical Haar from raw $\mu_v$ by precisely this factor. The [rendered p. 522 check](trace-moment-codimension-q.md#scope-and-handoff) confirms that (13.3.1.4) displays $\mu_v$ and no prefactor. The effective normalization under the prime is not yet verified from the rendered definitions. Section 14.1.2, p. 528, describes the intended divisor deduction, but does not provide the missing criterion.

The conditional premise used below is that the **capped critical-line sum equals the correctly normalized full-zero explicit distribution** on these one-sided, zero-integral real log tests. This could follow from a corrected Chapter 13 trace with the ordinary geometric terms, but not merely from the statement that Chapter 13 restates Chapter 12. The two trace statements use different spectral sums. Real test functions suffice in this premise because both distributions are complex linear.

## A one-sided moment uniqueness lemma

Let $W\subset\{w\in\mathbb C:|\Re w|\le a\}$, for $a\ge0$, have no finite accumulation points, and let $d_w\in\mathbb C$ satisfy $\sum_{w\in W}|d_w|/(1+|w|^2)<\infty$. For a nonnegative integer $D$ suppose

$$
\mathcal D(f):=\sum_{w\in W}d_w\int_0^\infty e^{wx} f(x)\,dx=0
\quad\text{whenever}\quad f\in C_c^\infty((0,\infty)),\quad \int_0^\infty x^j f(x)\,dx=0\quad(0\le j<D).
$$

Then $d_w=0$ for every $w\ne0$. The series defining $\mathcal D$ converges absolutely on the indicated smooth test space, even before imposing its moments: Integrate twice by parts against $e^{i(\Im w)x}$ and use the fixed bound on $\Re w$. If $D=0$, the same argument below gives $d_0=0$ as well when $0\in W$.

**Impose the moments without losing decay.** Choose fixed tests $h_0,\ldots,h_{D-1}$ with $\int x^k h_j(x)\,dx=\delta_{kj}$ for $0\le k,j<D$. To construct them, take $D$ smooth bumps of integral one shrinking around distinct positive points. Their moment matrix tends to a Vandermonde matrix, so for sufficiently narrow fixed bumps it is invertible. For $\Re z>a$ and fixed real $z_0>a$, take the [fixed-parameter cutoff difference](trace-to-zeros.md#fixed-parameter-subtraction-over-the-rationals)

$$f_{n,z}(x)=\chi(nx)\psi(x/n)(e^{-zx}-e^{-z_0x}),$$

where $0\le\chi,\psi\le1$ are smooth, $\chi$ is zero up to $1$ and one from $2$ on, and $\psi$ is one up to $1$ and zero from $2$ on. Subtract $\sum_j(\int x^j f_{n,z}(x)\,dx) h_j$ before using the hypothesis. The $j$th moment converges by dominated convergence to $j!(z^{-j-1}-z_0^{-j-1})$.

For $u=e^{\sigma x}f_{n,z}(x)$, $\sigma\in[-a,a]$, the $L^1$ norms of $u$ and $u''$ are uniformly bounded for $z$ on each compact subset of $\Re z>a$. The uncut weighted difference is $O(x)$ at zero with bounded first and second derivatives, and it and its derivatives decay exponentially at infinity. On the lower transition interval $[1/n,2/n]$, the differentiated cutoff costs at most $O(n^2 x+n)$ in the second derivative, with bounded integral. The upper transition costs are bounded by the exponential tail. Hence integration by parts bounds each transform by $C/(1+|w|^2)$, using the bounded real parts to pass from $|\Im w|$ to $|w|$. Dominated convergence in the zero sum gives

$$
\sum_{w\in W}d_w\left(\frac1{z-w}-\frac1{z_0-w}\right)
=\sum_{j=0}^{D-1} j!\left(z^{-j-1}-z_0^{-j-1}\right)\mathcal D(h_j).
$$

**Detect the orders.** On a compact set disjoint from $W$ the tail of the left series converges normally: The difference is $(z_0-z)/((z-w)(z_0-w))$. Near any $w_0\in W$, omit that single summand to obtain a holomorphic remainder across $w_0$, by the same estimate. The continued function therefore has residue $d_{w_0}$ there. By the meromorphic identity theorem it agrees with the right side, whose only possible pole is at $0$. This gives the result. A term at $w=0$ really is invisible if $D\ge1$, since it pairs with $\int f$.

## Application and formalization boundary

Take $w=\rho-1/2$ for distinct nontrivial zeta zeros and $d_w=\operatorname{ord}_\rho \zeta-\mathbf1_{\Re w=0}$. The classical count $O(T\log(2+T))$ with multiplicity gives the summability premise by dyadic decomposition, and the zeros are discrete with bounded real parts. The stated comparison is exactly the uniqueness hypothesis with $D=1$. It would imply that each noncentral zero is on the critical line and is simple. No positivity hypothesis or limit of trace widths is needed for this implication, and the proof cannot tell what weight occurs at the center. This is not the manuscript's proof, does not justify its clipped trace, and does not supply the corresponding comparison for arbitrary Hecke characters or number fields.

## Checked separation of the shifted zeta zeros

`Masullo.criticalStripZetaZeros` indexes distinct zeros with $0<\Re\rho<1$. `Masullo.shiftedZetaZero` is the injective translation $\rho\mapsto\rho-1/2$, with $|\Re(\rho-1/2)|<1/2$. For compact $K$, `shiftedZetaZero_preimage_finite` translates $K$ back, intersects it with Mathlib's ambient zeta zero set, and uses `IsCompact.inter_riemannZetaZeros_finite`. The index is countable by exhaustion by closed balls. This argument takes subsets of finite intersections; it does not assume that intersecting a closed set with the open strip preserves closedness.

`shiftedZetaZero_separated` gives the gap at **every** complex point $z$, including points not indexed by a zero. Within the closed unit ball about $z$, remove $z$ from the finite set of shifted zeros. Its open complement contains a ball about $z$. Taking the smaller of that radius and one gives the gap, also for all zeros outside the unit ball. These lemmas discharge the family hypotheses of `weight_eq_zero_of_zero_mass_annihilation` with $a=1/2$, independently of the trace comparison.

Independent Yah statement review confirmed that the compact-set finiteness, countable index, strip bound, injectivity, and every-point gap suffice for the geometric inputs, without an assumption at the strip boundary or a statement about the central weight.

The [quadratic summability lemma](trace-divisor-summability.md#checked-dyadic-shell-summability) gives the arithmetic input. The [checked specialization](trace-divisor-summability.md#checked-specialization-conditional-uniqueness-for-the-zeta-divisor) applies the uniqueness result to the full-minus-capped weights under the shared-test comparison. The comparison itself and the weight at the center remain separate.

## A pole test for the raw Haar reading

If (13.3.1.4) uses the full real-Haar kernel and its finite-place terms agree with the ordinary explicit formula, the capped formula and the ordinary full-zero formula are incompatible on this radial test class. The [rendered real-prime audit](trace-real-prime-q.md) gives that full-Haar value only by substituting the printed Fourier kernel; the additive definition gives half Haar. Its short-band witness does not replace the wider tests used by the pole argument. The earlier finite-place comparison used the extracted index sets and the fact that over $\mathbb Q$ the unit volumes are one. The short-band witness does not verify that comparison on the wider tests. This leaves exactly one extra real-place term in the difference between the full and capped sums. In fact the real additive Tamagawa measure is Lebesgue (Example A.3.1.5, p. 557), so using both signs in Definition A.3.2.2, p. 560, gives the ordinary kernel

$$H(x)=\tfrac12 e^{x/2}\left((e^x-1)^{-1}+(e^x+1)^{-1}\right)=\frac{e^{-x/2}}{1-e^{-2x}}\qquad(x>0).$$

Subtract the literal capped identity from the ordinary explicit formula. The raw-Haar reading gives $\mathcal D(f)=\int H(x)f(x)\,dx$ on zero-integral tests, with $\mathcal D$ the residual full-minus-capped distribution above. Apply this to the same moment-corrected cutoff differences at $D=1$. The uncorrected kernel integral converges to

$$L_H(z)=\int_0^\infty H(x)(e^{-zx}-e^{-z_0x})\,dx,$$

initially for $\Re z>1/2$. The subtraction removes the singularity of the integral at $0$. The difference between the zero-resolvent sum and $L_H(z)$ must then equal $(\mathcal D(h_0)-\int H h_0)(z^{-1}-z_0^{-1})$. However, $H-e^{-x/2}=O(e^{-5x/2})$ at infinity and $O(x^{-1})$ at zero. Its subtracted transform is holomorphic on $\Re z>-5/2$. Thus $L_H(z)$ has a pole of residue $1$ at $z=-1/2$, coming from $(z+1/2)^{-1}-(z_0+1/2)^{-1}$. Neither the moment correction nor the zero-resolvent sum has a pole there ($\rho=0$ is not a nontrivial zeta zero). Meromorphic identity is impossible. This tests the indicated reading against the ordinary explicit formula; it is not a visual reading, and does not rule out a corrected trace stated with canonical real-place Haar.

**Independent Yah review:** The review independently checked the pinned text and challenged the uniqueness proof and pole test. It confirmed the factor $1/M_v$, the finite sum comparison under the common index convention, and the possibility of hidden central weight. No rendered pages or Lean check were used.

The [cutoff interface](trace-divisor-cutoff.md) and [resolvent handoff](trace-divisor-resolvent.md#assembled-conditional-uniqueness) explain the checked composition. It does not use a capped-trace or geometric-normalization axiom. For the source branch, the local inconsistency prevents citing (13.3.1.3)–(5) as the comparison premise without a repair and a separate justification of the repaired capped trace.

# Smooth cutoff profiles for positive-log tests

**Status: Lean specialization and scalar limits.** [CutoffProfiles.lean](../../Proofs/Lemmas/CutoffProfiles.lean) implements a project repair for the [cutoff argument](trace-divisor-cutoff.md), not a manuscript theorem. It specializes the checked [pointwise](trace-divisor-cutoff-pointwise.md) and [integral](trace-divisor-cutoff-integral.md) bounds.

## Source gate

The digest-matched text extraction of pp. 519–520 and 522 gives the following provisional reading. Equation (12.5.1.4) evaluates the integrated smoothed geometric diagonal at a fixed strip $I=[-\alpha,\alpha]$ with full orders, citing Definition 10.4.3.7 and Theorem 10.4.2.8. Theorem 13.3.1.1 presents itself as that trace formula, but (13.3.1.2) imposes Mellin-jet vanishing, while (13.3.1.1) and (13.3.1.3) cap orders and keep only the line. Restricting to positive-log, zero-mean tests puts them in both domains over $\mathbb Q$ in the trivial compact isotype; it changes neither the operator in the preceding diagonal identity nor its coefficients. Continuity on the Chapter 13 subspace is not convergence of the Chapter 12 strip functionals as the width shrinks. Even a width limit deleting off-line terms would not clip excess orders on the line. No comparison of the two functionals is inferred. The p. 522 extraction also reads the note attached to Theorem 13.3.1.1 as “Correct statement.” No new visual check was performed; the [real-place normalization gate](trace-divisor-uniqueness.md#a-pole-test-for-the-raw-haar-reading) still applies.

### What the cited spectral cutoff can change

The digest-verified extraction of Theorem 10.4.2.8, p. 463, (10.4.2.20), takes $\Lambda\to\infty$ with $\varepsilon\Lambda=o(1)$ at fixed $I,s$. It traces $M_\rho A(\phi)P_a^{\mathrm{spec}}$, not a limit of projections as $I$ or $s$ varies. Definition 10.4.3.7, p. 473, (10.4.3.49)–(10.4.3.50), subtracts a weighted spectral kernel from the convolution kernel on $W_I^s$ for $s\ge3$; it does not compare Sobolev spaces or their geometric diagonals. Likewise, the trace-norm continuity in Theorem 10.3.2.1(2), p. 454, varies the test on a fixed spectral space, not the width or Sobolev exponent.

There is a **different** candidate for the cap: The trace formula cited by (10.4.2.20), namely (10.3.2.3)–(10.3.2.4), counts full orders in the strip interior but caps boundary orders at $\lfloor(s-1)/2\rfloor+1$. At $I=\{0\}$ this is a count on the line, also stated separately in (10.3.1.3)–(10.3.1.4), p. 448. Over $\mathbb Q$, choosing $s=2$ would give the desired cap **on the spectral side**. It does not instantiate the cited geometric kernel definition at $s\ge3$, where the Sobolev cap is at least two. The Chapter 12 sum (12.5.1.3), p. 519, is explicitly over the strip *interior*, so substituting $I=\{0\}$ in that sum is not the boundary count either. Restricting the test to the zero-mass subspace does not perform either replacement.

An independent Yah extraction review confirmed the fixed-cutoff mismatch. The [singleton diagonal audit](trace-divisor-singleton-diagonal.md) checks Theorem 10.4.3.4 (pp. 470–471) and its use in Chapter 12: The named kernels start at $s\ge3$, the singleton operator order is reversed, and the Hilbert–Schmidt representatives alone are not diagonal data. The project construction in that audit gives the correct-order global Haar diagonal at $s=2$ over $\mathbb Q$ in the trivial isotype. Its identification with the normalized local terms on the shared tests remains a separate obligation. No new image reading was performed.

## Lean interface

Write $\chi(t)=\operatorname{smoothTransition}(t-1)$. `Masullo.cutoffTest` is

$$f_N(x)=\chi(Nx)(1-\chi(x/N))(e^{-zx}-e^{-z_0x}).$$

- `Masullo.cutoffTest_uniform` assumes $a<\Re z$ and $a<z_0$. It gives a single constant for all real scales $N\ge2$ bounding the sum of the two $e^{ax}$-weighted integrals of $|f_N|$ and $|f_N''|$ on $x>0$. The same theorem gives smoothness on all of $\mathbb R$, compact support, and topological support strictly above zero. No zero-mass or spectral hypothesis is needed.
- `Masullo.cutoffTest_eq_at_large_scale` gives exact equality with the exponential difference at any positive point $x$ as soon as the positive scale satisfies $N\ge\max(2/x,x)$, including the endpoints. This is a pointwise statement, not an assertion of a common scale of equality or of convergence of derivatives.
- `Masullo.tendsto_positiveLaplaceTest_cutoffTest` takes $N=(n:\mathbb R)+2$ and $\Re w<\min(\Re z,z_0)$. It proves convergence to $(z-w)^{-1}-(z_0-w)^{-1}$. The common integrable envelope on $x>0$ is $2\exp(-\delta x)$ with $\delta=\min(\Re z,z_0)-\Re w>0$, using the undifferentiated cutoff factors in $[0,1]$. The derivative-layer estimate is not used for scalar dominated convergence. The Bochner integrals of the two exponentials are evaluated separately.
- `Masullo.tendsto_cutoffTest_mass` is the $w=0$ specialization, exposed as a restricted half-line integral with limit $z^{-1}-z_0^{-1}$. It requires $0<\Re z$ and $0<z_0$, which follow in the planned application from $0\le a<\min(\Re z,z_0)$.

The uniform bound uses the vanishing of the first two derivatives of $\chi$ off $[1,2]$ and compactness of that interval. Scaling gives factors $N,N^2$ in the lower layer and $N^{-1},N^{-2}$ for the upper cutoff. The lower layer needs the linear estimate for the **weighted** exponential difference: Its exponents are shifted by $-a$, and the difference vanishes at zero. The support argument passes from the pointwise support to its closure inside the closed interval $[1/N,2N]$.

## Next and checks

Independent Yah statement review confirmed the half-line domain, sign, decay conditions, and mass specialization. The release checks are `lake --wfail build Proofs`, `lake env leanchecker Lemmas.CutoffProfiles`, and `#check` and `#print axioms` for the public declarations.

Next, prove the mass-corrected series limit. Use the uniform integral estimate and `Masullo.norm_positiveLaplaceTest_mul_weight_le` for the summable majorant $C\|d_i\|/(1+\|w_i\|^2)$ under the separate weighted summability premise, and the scalar limit for each $w_i$. Apply annihilation only to $f_N-M(f_N)h$ for a **fixed** mass-one bump $h$. The full-versus-capped distribution identity remains an explicit premise, not a consequence of the profile or limits.

# Smooth cutoff profiles for positive-log tests

**Status: Lean specialization.** [CutoffProfiles.lean](../../Proofs/Lemmas/CutoffProfiles.lean) implements a project repair for the [cutoff argument](trace-divisor-cutoff.md), not a manuscript theorem. It specializes the checked [pointwise](trace-divisor-cutoff-pointwise.md) and [integral](trace-divisor-cutoff-integral.md) bounds.

## Source gate

The digest-matched text extraction of pp. 519–520 and 522 gives the following provisional reading. Equation (12.5.1.4) evaluates the integrated smoothed geometric diagonal at a fixed strip $I=[-\alpha,\alpha]$ with full orders, citing Definition 10.4.3.7 and Theorem 10.4.2.8. Theorem 13.3.1.1 presents itself as that trace formula, but (13.3.1.2) imposes Mellin-jet vanishing, while (13.3.1.1) and (13.3.1.3) cap orders and keep only the line. Restricting to positive-log, zero-mean tests puts them in both domains over $\mathbb Q$ in the trivial compact isotype; it changes neither the operator in the preceding diagonal identity nor its coefficients. Continuity on the Chapter 13 subspace is not convergence of the Chapter 12 strip functionals as the width shrinks. Even a width limit deleting off-line terms would not clip excess orders on the line. No comparison of the two functionals is inferred. The p. 522 extraction also reads the note attached to Theorem 13.3.1.1 as “Correct statement.” No new visual check was performed; the [real-place normalization gate](trace-divisor-uniqueness.md#a-pole-test-for-the-raw-haar-reading) still applies.

## Lean interface

Write $\chi(t)=\operatorname{smoothTransition}(t-1)$. `Masullo.cutoffTest` is

$$f_N(x)=\chi(Nx)(1-\chi(x/N))(e^{-zx}-e^{-z_0x}).$$

- `Masullo.cutoffTest_uniform` assumes $a<\Re z$ and $a<z_0$. It gives a single constant for all real scales $N\ge2$ bounding the sum of the two $e^{ax}$-weighted integrals of $|f_N|$ and $|f_N''|$ on $x>0$. The same theorem gives smoothness on all of $\mathbb R$, compact support, and topological support strictly above zero. No zero-mass or spectral hypothesis is needed.
- `Masullo.cutoffTest_eq_at_large_scale` gives exact equality with the exponential difference at any positive point $x$ as soon as the positive scale satisfies $N\ge\max(2/x,x)$, including the endpoints. This is a pointwise statement, not an assertion of a common scale of equality or of convergence of derivatives.

The uniform bound uses the vanishing of the first two derivatives of $\chi$ off $[1,2]$ and compactness of that interval. Scaling gives factors $N,N^2$ in the lower layer and $N^{-1},N^{-2}$ for the upper cutoff. The lower layer needs the linear estimate for the **weighted** exponential difference: Its exponents are shifted by $-a$, and the difference vanishes at zero. The support argument passes from the pointwise support to its closure inside the closed interval $[1/N,2N]$.

## Next and checks

An independent Yah statement review confirmed the two theorem types and the formula for `cutoffTest`, the match to `Masullo.norm_positiveLaplaceTest_mul_weight_le`, and the provisional manuscript boundary above using the digest-verified PDF. The release checks are `lake --wfail build Proofs`, `lake env leanchecker Lemmas.CutoffProfiles`, and `#check` and `#print axioms` for the public declarations.

Use $N=(n:\mathbb R)+2$. First prove the scalar positive-half-line transform limit to $(z-w)^{-1}-(z_0-w)^{-1}$ for $\Re w\le a$. The fixed integrable envelope is $2\exp(-\delta x)$ with $\delta=\min(\Re z,z_0)-a>0$, from the undifferentiated cutoff factors in $[0,1]$. The moving derivative layer is not such an envelope. With $0\le a$, the same scalar limit at $w=0$ gives the mass limit. Without positive decay at $w=0$, a mass limit need not exist, even when the uniform weighted bound holds.

The uniform integral estimate and the compact-test bound give a majorant for dominated summation after imposing the separate weighted summability hypothesis. Apply annihilation only to $f_N-M(f_N)h$ for a **fixed** mass-one bump $h$. The full-versus-capped distribution identity remains an explicit premise, not a consequence of the profile or limits.

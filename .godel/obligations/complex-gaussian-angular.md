# The complex Gaussian is indexed by the same angular weight

**Verdict.** The printed complex test in Definition 3.4.3.2, p. 152,
cannot give the Gamma factor (3.2.1.5), p. 123, under the calibration
(3.4.3.12), factorization (3.4.3.13), and bilinear integral (3.3.1.7),
p. 130. At $c_v(re^{i\theta})=r^4e^{i\theta}$ the printed pairing
converges absolutely to zero, while the Gamma factor at squared-norm
exponent $s=2$ is $(2\pi)^{-5/2}\Gamma(5/2)>0$. Using the raw zero
as the Gaussian scalar does not recover that Gamma factor or fix the
separate covariance mismatch below. Neither check refutes the existence
of a correctly normalized local zeta distribution or an independently
defined Hecke functional equation.

## Rendered readings

This is the prior angular branch handoff, not a new source check from
the finite normalization run.

The local PDF matches the SHA-256 pin `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. Chapter 3 and Appendix A Markdown were read before using numbered layout to locate the passages. Poppler 270 dpi grayscale pixel crops were inspected via direct Unicode braille renderings, not inferred from extraction. Independent reviewer `OjTLgPn` (`angular-source-review` in Yah session `01a20177-6927-7d0b-ad78-865488044f5f`, read-only output `b5c7a743664f408133f12d1dbcb5854de6abe69e`) separately confirmed the decisive bars, indices, and covariance reading.

- Definition 3.4.3.2, p. 152, selects $\omega_v=\omega_{t,m}:re^{i\theta}\mapsto r^t e^{im\theta}$. Equation (3.4.3.5) uses the unbarred $z^m$ for $m\ge0$, and (3.4.3.6) uses $\bar z^{-m}$ for $m<0$. In both, the coefficient is $1/(2\pi)$, and the exponential is $e^{-2\pi z\bar z}$. The sentence between (3.4.3.8) and (3.4.3.9) associates $E_{c,v}$ to $c|_{C_F^1}$, not its inverse; the tensor in (3.4.3.9) uses $E_{c_v,v}$.
- Theorem 3.4.3.3(1) starts on p. 152 with every $c\in\Omega(F_v^\times)$ and the local multiplicative Tamagawa measure. Equation (3.4.3.12), p. 153, puts $E_{c_v,v}$ in $\langle\Delta'_v(c),E_{c_v,v}\rangle=1$, with neither a bar nor inverse in the index. Equation (3.4.3.13) prints $Z_v(\cdot,c)=L_v(c)\Delta'_v(c)$, with the same character.
- Equation (3.3.1.7), p. 130, integrates $f_v(g)c_v(g)$ over $F_v^\times$ against $\mu_v$, without conjugation or inversion. Theorem 3.4.3.3(1) describes (3.4.3.13) as meromorphic; the witness is a regular point where the integral itself converges.
- The definition of $\Omega$ in §3.1.1, p. 118, uses continuous homomorphisms into $\mathbb C^\times$. Equations (3.1.1.1)–(2), p. 119, use restriction to the norm-one subgroup and the exponent of the module. Section 3.1.2.1, p. 121, explicitly uses the squared Euclidean norm at a complex place. The witness is $e^{i\theta}|z|_v^2$ and has angular weight one and zero unitary radial frequency. Section 3.1.2.2, p. 121, identifies $c_v=c\circ j_v$, not its inverse.
- The p. 123 prose before (3.2.1.5) writes $(r,\theta)\mapsto r^s e^{in\theta}$ alongside $\chi_v|\cdot|_v^s$. For consistency with the latter and p. 121, the radial variable in that line must be the squared norm. If instead read as Euclidean radius, it labels this same witness by $s=4$ and still gives a positive Gamma value. That ambiguity does not affect the zero-versus-nonzero verdict. The $5/2$ value here uses the normalized norm in the displayed argument of (3.2.1.5).
- Definition A.3.1.2(2), p. 556, gives $2\,dx\,dy$; Definition A.3.2.2(1), p. 560, divides by the normalized absolute value off zero. Thus the density in polar coordinates is $2\,dr/r\,d\theta$. The argument for zero only needs invariance, not this calibration.

## The weight-one control and its scope

With $z=re^{i\theta}$, $E_{c_v,v}c_v=(2\pi)^{-1}r^5e^{-2\pi r^2}e^{2i\theta}$. Its absolute radial integral is bounded by a constant times $\int_0^\infty r^4e^{-2\pi r^2}\,dr<\infty$. Rotation $z\mapsto iz$ negates the integrand while preserving Haar. Replacing just the monomial $z$ by $\bar z$ makes the angular part one. The angle cancels $1/(2\pi)$ and $t=r^2$ leaves $\int_0^\infty t^{3/2}e^{-2\pi t}\,dt=(2\pi)^{-5/2}\Gamma(5/2)$. More generally for $c_v=u^m(r^2)^{s+i\tau}$ with $u=z/r$, $m\in\mathbb Z\setminus\{0\}$, $\tau\in\mathbb R$, and $\Re s>0$, rotation by $e^{i\pi/(2m)}$ gives the same zero for the printed test. The bar switch replaces $m$ by $-m$ in the polynomial and leaves the degree $|m|$; it does not change weight zero.

The local quantifier already admits the witness. To also meet the globally worded definition of $E_{c,v}$ literally, take $F=\mathbb Q(i)$, choose a generator $a$ of the finite fractional ideal of an idele $x$, and choose the residue character $\eta$ at $(2+i)$ carrying the reduction of each Gaussian unit $u$ to $u^{-1}$ (the four units reduce bijectively onto $\mathbb F_5^\times$). The product of the complex phase of $x_v/a$ with $\eta(x_{(2+i)}/a\bmod(2+i))$ is independent of $a$, multiplicative, continuous on the finite-unit neighborhood of 1 and hence everywhere, and trivial on principal ideles. Its local restriction is $e^{i\theta}$, and the squared-norm twist gives the witness. The global norm-one restriction has the same value on the inserted circle. This is an ordinary construction, not a Lean endpoint.

**Separate covariance check.** The rendered Definition 3.4.3.1(1), p. 151, sets $\rho'_v(g,T)=c(g)T$ and $\rho'_v(g,T)(f)=T(f\circ m_g)$ with $m_g$ multiplication by $g$. Haar substitution gives $Z_v(f\circ m_g,c)=c(g)^{-1}Z_v(f,c)$ on its domain of absolute convergence. The repaired nonzero test shows $c(i)=i$ versus $c(i)^{-1}=-i$. Thus conjugating the polynomial fixes the scalar value but not the full eigendistribution formulation, which also needs a consistent action or weight index. This is a check of the printed definitions, not of the cited classification.

## Lean and next check

Accepted `Masullo.complexGaussianZetaDensity_integral` in [ComplexGaussianMellin.lean](../../Proofs/Theorems/ComplexGaussianMellin.lean) proves the opposite-weight repair for all integer $m$, real radial frequency $\tau$, and $\Re s>0$, against the Tamagawa density on complex coordinates. Since the earlier handoff, accepted `4e37ced863adec2785cb30724b80b45cdad023ee` also transports this to actual complex completion-unit Haar for every unitary Mathlib Hecke character and $\Re s>0$, via `Masullo.complexCompletionGaussianPair` in [ArchimedeanCompletionGaussian.lean](../../Proofs/Theorems/ArchimedeanCompletionGaussian.lean). These are local integral theorems, not Lean checks of the printed mismatch, covariance, or global product.

The successor [finite normalization check](finite-gaussian-tamagawa.md)
is now resolved at the place over 2 of $\mathbb Q(i)$. It is independent
of the complex angular check, and neither local result is a global
factorization.

The general-field restricted-product Haar and completed-product identification, conductor assembly, reflected-line integrability, and contour exhaustion are separate. The earlier [global Mellin sign](global-mellin-sign-q.md) is unchanged, and the [unadopted modulus-three Fourier recovery](hecke-right-line-majorant.md#open-ramified-local-conductor-power-in-the-general-reflection) has a full saved-revision pointer in the accepted note.

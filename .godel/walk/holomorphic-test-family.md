# The holomorphic test family: Which character is approximated?

**Status: Open as printed.** Masullo, *The Music of the Primes*, §1.4.2,
“An explicit holomorphic family of test functions,” claim beginning
on printed p. 28 and ending with the pointwise convergence sentence
on p. 29. The chapter Markdown and PDF layout extraction located
this passage in the [pinned, digest-verified edition](../sources/masullo/README.md).
Raster OCR checked the surrounding prose and the continuation before
§1.4.3. Direct inspection of rendered pixel crops checked the exponent
−z, the value 1/2 at t = 1, the absence of a bar above χ in the target
χ·φ_z, the cutoff times convolution display, and the exclusion t ≠ 1
in the convergence sentence.

Masullo sets φ_z(t) = t^(−z) for t > 1 and zero for 0 < t < 1,
with φ_z(1) = 1/2. He proposes to approximate χ·(φ_z ∘ |·|_F) by
smooth compact tests satisfying the preceding test conditions and
homogeneous for the conjugate of a chosen Hecke character. The scalar
construction is h(t)(ρ_ε * φ_z)(t), where h is a smooth compact bump
supported in (1,∞), valued in [0,1], and tending monotonically to the
indicator of (1,∞). The monotonicity is of h, not of the complex-valued
mollified tests.

## Scalar construction versus character lift

For a compactly supported smooth approximate identity in the real t
coordinate (extend the scalar profile by zero below 1), convolution
converges at every t ≠ 1. Multiplication by h gives the claimed scalar
pointwise limit there. At fixed h and ε the family is entire in z:
The integration variable where the input is nonzero ranges over a
bounded interval in [1,∞) on the support of h, so differentiating
exp(−z log t) is locally uniformly dominated. Compact support strictly
above 1 forces vanishing on the norm-one fibre and excludes its assigned
value 1/2 from the approximation. The scalar argument is Masullo's
construction with the usual approximate-identity hypotheses made
explicit by the reviewer. Pointwise convergence alone supplies no
uniform bound for a subsequent trace or a sum over zeros.

For the fixed unitary χ of [§1.4.1](characterwise-trace-formula.md),
right-translating the printed target by k ∈ C_F¹ multiplies it by
χ(k), not χ̄(k). A pointwise limit of tests of weight χ̄ retains that
weight: Apply the limit at g and gk, which lie on the same norm fibre.
Since the proposed radial profile is nonzero at every norm above 1,
the two weights have to agree on C_F¹ for that approximation to work
with the same χ. The manuscript's “chosen Hecke character” could instead
mean χ̄, but then the fixed character in the trace formula must also
be relabelled, including its spectral pairing. For the original fixed χ,
the admissible lift would use χ̄·(h(ρ_ε * φ_z) ∘ |·|_F) and target
χ̄·(φ_z ∘ |·|_F). Neither repair establishes the fixed-character use as
printed. The missing step is one consistent choice of character for the
target, the lifted approximants, and the Mellin pairing, or a stated
self-conjugacy restriction on C_F¹.

The project's [smooth cutoff profile audit](../obligations/trace-divisor-cutoff-profiles.md)
concerns a different construction. `Masullo.cutoffTest` uses two cutoffs
of a difference of exponentials in the real log coordinate without
mollification or a character lift. Its scalar Laplace limit
`Masullo.tendsto_positiveLaplaceTest_cutoffTest` is for that difference
under the two decay inequalities, not this family on C_F. No new Lean
result is claimed here.

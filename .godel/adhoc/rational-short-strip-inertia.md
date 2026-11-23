# Rational short-strip inertia: checked upper bounds and the lower-bound gap

This is the scalar short-interval problem from `rational-strip-inertia.md`.
It does not concern the fixed-pulse variant or identify the scalar form with
an ordered geometric trace.

## Endpoint and conventions

Let `I = (l,r)` be nonempty, with `0 < l < r < log(2)/2`. The real
vector space is `V = {u ∈ C_c^∞(I) : ∫ u = 0}`. Set
`M_u(z) = ∫ u(x) exp(zx) dx`. The profile used in the trace is **ordinary**
convolution `u*v`; in particular no adjoint or reflection is applied to `v`.
For `0 < a < 1/2`, write `w = ρ - 1/2` for a nontrivial zeta zero and
`m_w` for its full analytic order. The form and omitted divisor are

```
B_a(u,v) = -Σ_{|Re w| < a} m_w M_u(w) M_v(w),
O_a      = {w : a ≤ |Re w|}.
```

Each location is used once in the sum and weighted by `m_w`. The two
edges belong to `O_a`. The target is negative index exactly `1 + k_a`,
where `k_a` counts **distinct** omitted conjugate pairs, not orders and
not functional-equation quartets. For `B_a + M(1/2) ⊗ M(1/2)` the target
is exactly `k_a`. Infinite index means arbitrarily large finite-dimensional
strictly negative subspaces. In the source, quartet symmetry gives even
`k_a` when finite, so index at most two would force `k_a = 0`. The small-width
RH criteria in the note use the exact index (in particular its lower bound),
not merely the scalar identity or the upper bound below.

## Lean bridge on the actual zeros

* `rationalRadial_fullTrace` is the normalized full-order scalar explicit
  formula. `rationalRadialStripTrace_iff` compares the normalized scalar
  identity on *all* radial profiles with inclusion of every zero in the
  open strip; it is not an inertia theorem. The existing
  `exists_rationalShortWindow_stripTrace_separation` uses a dyadic count
  hypothesis to find a single reflected profile: the full-order strip
  sum and the normalized local/polar pairing vanish, but the model density
  pairing is nonzero. That profile is not required to be `u*u`, and the
  conclusion does not approximate independent finite coordinates with
  the archimedean norm small.
* `rationalShortWindow_fullTrace` in
  [`RationalShortWindowStripTrace.lean`](../../Proofs/Theorems/RationalShortWindowStripTrace.lean)
  evaluates the full formula for a smooth real profile supported in
  `(L, log 2)`, `L > 0`, with **positive** log coordinate. Both signs of
  every prime-power argument miss the support, and the identity value is
  zero. The half-Haar fold is `exp(-x/2)/(1-exp(-2x))` on this support.
  Expansion by a dominated geometric series cancels the `n=0`
  term with the pole at `-1/2`, leaving the pole at `+1/2` with a minus
  sign in the negative full sum.
  `rationalIdeleRadialMellin_eq_shiftedCompactLogMellin` makes the
  change from radial parameter `s` to log exponent `s-1/2` explicit.
* `rationalShortStripTrace_decomposition` in
  [`RationalShortStripInertia.lean`](../../Proofs/Theorems/RationalShortStripInertia.lean)
  applies that evaluation to the ordinary convolution. The support of
  `u*v` lies in the sum of the two compact supports, inside `(2l,2r)`;
  `compactLogMellin_convolution` gives the product of the two moments.
  Absolute summability of the full product terms follows from the full
  formula for this profile. `rationalShortStripTrace_radial_hasSum`
  identifies the product-coordinate form with minus the convergent
  normalized radial strip sum on `u*v`. Interior and omitted indices are
  complementary subsets of `criticalStripZetaZeros`, disjoint and exhaustive, so the
  formula applies to the strict strip without dropping edge zeros. In
  particular, with `λ_n = -2n-1/2`, the checked identity is

  ```
  B_a(u,u) = Σ_{n≥1} M_u(λ_n)^2 - M_u(1/2)^2 + Σ_{w∈O_a} m_w M_u(w)^2.
  ```

  Lean gives the bilinear product version as a `HasSum` and does not need
  mass zero, the density estimate, or a restriction on `a` for this identity.
  `rationalShortStripTrace_real` verifies reality by reindexing under
  conjugation: location, strip membership, and analytic order are
  preserved, and the Mellin moments conjugate.
  `rationalShortStripBilinForm` packages the real part as a bilinear form on
  the mass-zero test space, using moment linearity and absolute summability.
  `rationalShortStripBilinForm_symm` checks its symmetry.
* `rationalShortStripTrace_polarCorrected_nonneg` checks nonnegativity
  of the corrected form when the imaginary moments at the omitted
  **positive-ordinate** representatives vanish. Positive/zero/negative
  ordinate is exhaustive; negative ordinates are conjugates of positive
  ones, and at zero ordinate the moment is already real. Thus any real
  omitted zero would contribute only a nonnegative square; no exclusion
  of real zeros is needed in this Lean proof. In the pair notation, each
  nonreal pair contributes `2 m_w ((Re M_u(w))² - (Im M_u(w))²)`:
  conjugation gives exactly one representative above and one below the
  real axis, their orders agree, and their squares add to twice the real
  part. This explains why order weights do not increase the count of
  possible negative directions.
* `rationalShortWindowTests` is the mass-zero submodule on the specified
  interval. `rationalShortStripTrace_finrank_bounds` checks the two upper
  bounds on negative subspaces `W` of this actual test space, given a
  finite type of omitted positive-ordinate locations. The map to the
  corresponding imaginary moments is injective on a strictly negative
  subspace for the corrected form, by the preceding kernel nonnegativity;
  adding the real pole coordinate gives the injection for the uncorrected
  form. Lean concludes finite-dimensionality of `W` and the respective bounds
  `finrank W ≤ k_a` and `finrank W ≤ 1+k_a`. Neither asserts that a subspace
  attaining the bound exists.

## What the lower bound needs

The following explains the paper argument and isolates unformalized steps;
none is an additional hypothesis of the checked upper bounds.

1. **Fixed-width arithmetic input.** At `σ = 1/2 + a > 1/2`, Ingham's
   density bound gives a count `O_a(T^θ (log T)^C)` of right-sector zeros
   through height `T`, with `θ = 3(1-σ)/(2-σ) < 1` and a fixed log power
   `C` (classically `C = 5`). Bound the number of distinct locations by the
   order-weighted count and absorb the log factor
   in an exponent `θ'` with `θ < θ' < 1`. On height bins below `2^(j+1)`
   this gives the dyadic bound `C_a q^j` with `q = 2^θ' < 2`. Reflection
   and conjugation transfer it to the omitted tail. This is precisely
   where `exists_omittedZetaTail_reciprocal_budget` in
   `Props.OmittedZetaTailBudget` would apply: a sufficiently high tail has
   arbitrarily small sum of `1/|Im w|`. The cited count is from the source
   note (see also [Chourasiya–Simonic, Corollary 1](https://arxiv.org/abs/2507.15184v2));
   the repository budget is conditional and does not prove Ingham. No
   estimate at `a=0` is required. If the omitted set is finite, no count is
   needed for the lower-bound strategy: use the finite polynomial alone.
   In the paper argument the absence of
   real strip zeros follows from the positive alternating eta series on
   `0<s<1`, with `η(s) = (1-2^(1-s))ζ(s)`.
2. **Filtering without losing the selected coordinates.** Fix a finite
   subset of positive-ordinate representatives `w_j` and an interval `J`
   compactly inside `I` with slack on the right. For each high unwanted
   `w=b+it`, `t>0`, use the probability supported at `0` and `h=π/t`
   whose transform is `(1+exp((z-b)h))/(1+exp(-bh))`. It kills both `w`
   and `conj w`. Choose the tail above every selected ordinate and with
   total displacement smaller than the slack. Its infinite convolution
   is the law of the sum of the bounded displacements. Each factor is
   positive on real arguments and nonzero at each selected `w_j` (the
   imaginary phase has absolute value strictly less than `π`). At any
   fixed retained argument the factor differs from one by `O(h)`
   uniformly in `|b|≤1/2`, so the product is nonzero there as well. A
   finite real polynomial `p` with roots at `0` and the remaining
   unwanted locations kills those without killing `1/2` or a selected
   point. On the resulting tests `u=p(-D)(μ*φ)`, `φ∈C_c^∞(J;ℝ)`, mass
   zero and support in `I` hold and `M_u(z)=c(z)M_φ(z)` for
   `c(z)=p(z)M_μ(z)`. Nonnegative displacements yield
   `|c(λ_n)|=O((1+n)^deg p)`. The conditional compact filter machinery
   supplies related support and vanishing statements, but its use with
   preservation of all the selected coordinates of this test family is
   not checked here.
3. **Simultaneous separation, not individual interpolation.** For this
   *filtered* family the required closure statement in the real Hilbert
   space `ℓ²(ℕ≥1;ℝ) × ℝ × ℂ^k` is

   ```
   closure { ((M_u(λ_n))_{n≥1}, M_u(1/2), (M_u(w_j))_j) : u filtered }
       ⊇ {0} × ℝ × ℂ^k.
   ```

   A continuous real annihilator has an `ℓ²` archimedean coefficient
   sequence and finite real/complex coefficients. Testing against every
   `φ` gives, on `J`, an equality between the archimedean series with
   terms `A_n c(λ_n) exp(λ_n x)` and a finite exponential polynomial
   with exponents `1/2`, `w_j`, and their conjugates. The archimedean
   series is locally normally convergent for `Re x>0` (geometric decay
   dominates the polynomial bound) and decays like `exp(-5x/2)` as real
   `x→+∞`. Analytic continuation preserves the equality there. A
   nonzero finite exponential polynomial with these distinct exponents
   cannot decay that fast: divide by the exponential for the largest
   real part, use the long-interval mean square to extract the squared
   coefficients at that real part, and repeat on the remaining terms.
   Nonvanishing of `c` at the retained points makes all finite
   coefficients zero. The double-annihilator argument then gives the
   closure claim. This archimedean-plus-finite argument is not a
   consequence of the existing one-witness separation theorem and is
   not formalized here.
4. **Realization of the index.** With all unwanted moments zero, the
   diagonal formula is a continuous quadratic form in the joint Hilbert
   coordinates above. Approximate the pole direction and the `k` purely
   imaginary selected directions with small archimedean norm; their
   limiting Gram matrix is strictly negative definite (diagonal entries
   `-1` and `-2m_{w_j}`). Strict negativity persists under simultaneous
   approximation in finite dimension, which also makes the chosen tests
   linearly independent. Omit the pole direction for the corrected form.
   This would give the matching lower bound when the omitted set is
   finite, or arbitrarily large negative subspaces when it is infinite.
   This step and its required closure input are not yet Lean endpoints.

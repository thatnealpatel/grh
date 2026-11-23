# §1.2.1 — finite rational Mellin jet blocks, not the Hilbert trace

Proof lane `680aa354d701f75bfe15c1869edd5f894dbc46686e383345c36ff268726facd6`,
Walk revision `06096d2a7c18e6cd94b2a8509df37fd99a52d43a7be75bc610b9514c298bb55e`.
[Receipt](680aa354d701f75bfe15c1869edd5f894dbc46686e383345c36ff268726facd6-06096d2a7c18e6cd94b2a8509df37fd99a52d43a7be75bc610b9514c298bb55e.json).
Writer base `0c66aa8549fbe74761d9ddd15b019e4d1a704048`; owning check session
`01a20628-5261-79af-a229-aa659c01a69d`. The owning integration handoff
records final candidate checks, independent review, and disposition.

## Printed claim and proof steps

Verified the local PDF against the [edition pin](../sources/masullo/README.md):
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Printed pages equal one-based PDF ordinals below. For reproducible source
inspection, use `pdftoppm -f N -l N -r 210 -gray -singlefile "$pdf" pageN`;
layout extraction supplies navigation, with raster OCR and a direct crop
of the p. 14 diagonal/rank line for the formula reading.

- **§1.2.1, pp. 13–14.** On p. 13 read items (1)(a)–(b), (2), and the
  unnumbered interior trace sum: the base is symmetric of arbitrary positive
  width, the test is supported strictly above norm one, and the highlighted
  degree is zero. On p. 14 the preceding display defines inverse-left
  convolution, `(A(φ)g)(x) = ∫ φ(y)g(y⁻¹x) dμ(y)`. The assigned paragraph,
  “This is computed using the Schauder basis”, is on the **original Fréchet
  quotient isotype's strong dual**, not stated solely on the Hilbert dual.
  It selects the evaluations and derivatives with shifted zero in the strip,
  cites Fréchet-side nuclearity to compute the completed quotient trace by the
  transpose, and calls the blocks Jordan blocks, with common diagonal
  `M(φ)(χ|·|_F^(ρ−1/2))` and rank equal to multiplicity. The separate p. 14
  rank-one expansion beginning “Explicitly” and the later kernel paragraph
  are outside this assignment.
- **Theorem 7.1.4.2(2)–(3), pp. 326–330.** The map (7.1.4.5) into the
  strong annihilator is claimed injective with dense image; (7.1.4.6)–(7)
  describe the evaluations and biorthogonal space. The indices here are
  **all** zeros. The source tests with (7.1.4.12), the entire factor
  divided by `(s−ρ)^(N(ρ)−m)` on p. 329, and obtains triangular vanishing
  in (7.1.4.18)–(19) on p. 330, allowing a finite change to exact
  biorthogonality. Testing (7.1.4.20) proves uniqueness for a series already
  converging to zero, not convergence of partial sums for every dual vector.
  Even granting the asserted all-zero result, if a jet is omitted, its
  Fréchet-quotient biorthogonal vector `v` gives a continuous linear
  functional `ℓ ↦ ℓ(v)` on the strong dual (the singleton `{v}` is bounded).
  This vanishes on the retained span and its closure but is one on the
  omitted jet. This obstruction is conditional on an omitted jet; no
  off-line zero is asserted.
- **Theorems 9.3.2.6 and 10.2.2.1, pp. 426 and 446.** The latter uses
  (10.2.2.4)–(6) for the weighted jets, interior multiplicities and edge
  caps, and calls its Hilbert-side result *Markushevich*, not Schauder.
  Its proof invokes the former. In (9.3.2.10), increasing the ordinate
  cutoff adds conditions to an **intersection of kernels**, so the
  subspaces decrease, whereas the proof claims the opposite inclusion.
  Projectors onto those decreasing subspaces cannot converge strongly to
  identity if any one subspace is proper. This does not adjudicate the
  Hilbert totality claim itself. In the rational radial model, an order
  `m` edge functional must have `2m+1<s` (the reciprocal-weight square
  integrand on the nondecaying half-line behaves as `|x|^(2m−s)`). Thus
  at `s=0` not even an edge evaluation is a Hilbert jet.
- **(10.3.1.8)–(10.3.1.17), pp. 449–450.** The singleton calculation
  expands `log|gy| = log|g| + log|y|`; (10.3.1.12) expresses the transpose
  action as a binomial sum of lower derivatives. The coefficient and
  vanishing in (10.3.1.13)–(14) give the triangular array in (10.3.1.17),
  with Mellin multiplier at the corresponding spectral point on each
  diagonal entry. The interval theorem 10.3.2.1, pp. 453–455, assumes
  **`s>1`** in its opening line; (10.3.2.3)–(5) use its interval cutoffs
  and multiplicities. It is not an `s=0` proof. Lemma C.3.2.2, p. 695,
  (C.3.2.5), compares nuclear traces under a continuous injection with
  a compatible **nuclear factor** in the reverse direction and approximation
  properties. Merely naming a Fréchet nuclear operator and a Hilbert
  completion does not exhibit this factor.

## Checked local calculation and its limit

[`Theorems.RationalMellinDivisorJetBlock`](../../Proofs/Theorems/RationalMellinDivisorJetBlock.lean)
works for `ℚ`, `χ=1`, and compact continuous log profiles with normalized
radial Haar `dx`. The [accepted rational divisor kernel](rational-mellin-divisor-kernel.md)
identifies the points `shiftedZetaZero ρ = ρ−1/2` and their positive orders.
`compactLogMellin` uses the positive exponent `e^(zx)` and the real
convolution uses `g(x−y)`, so integrating the convolution with `e^(zx)`
is equivalent to convolving the two exponentially weighted profiles and
integrating; their integrability follows from compact support and continuity.
This uses the actual log convolution, not a stipulated product action.

Leibniz's rule after division by factorials gives row `i`, column `j`
entry `M(φ)^(i−j)(ρ−1/2)/(i−j)!` if `j≤i`, zero otherwise. The rows
encode the image jet coordinates as functions of the input jet coordinates;
in the corresponding ordered basis of dual functionals the matrix is its
transpose. Passing from the printed unnormalized derivative coordinates
to Taylor coordinates removes the binomial factors and preserves trace.
The checked theorem applies this matrix to the **existing** normalized
`rationalMellinDivisorJet` of the input Mellin transform. It is a calculation
at one zero at a time, with the full divisor jet length, before imposing any
strip, Sobolev degree or theta quotient. It does not assert arbitrary
interpolation in the compact-profile space or identify a matrix of the
completed Hilbert operator. The finite trace is `N(ρ) M(φ)(ρ−1/2)`;
the determinant is zero iff this multiplier value is zero. Even `φ=0`
is a smooth test supported strictly above norm one (empty support) and
produces a rank-zero matrix of positive size at any such zero. Multiplicity
is the **dimension**, not automatically rank; a lower triangular jet matrix
need not be a single Jordan block.

The [accepted bounded convolution](rational-radial-hilbert-convolution.md)
constructs `rationalRadialQuotientConvolution` compatible with projection to
`rationalRadialHilbertQuotient`. It is not a trace-class result. The
[accepted edge result](rational-radial-boundary-jet.md)
`rationalRadialQuotient_boundaryJet_lt` is a necessary criterion for a
continuous extension, not a joint-kernel theorem. The accepted entire
kernel and interpolation (`rationalMellinDivisorJet_kernel`,
`entireDivisorJet_surjective`) do not identify the Hilbert theta closure.
The [positive even-degree restricted rational repair](../obligations/trace-spectral-strip-q.md)
does not give degree zero, arbitrary widths, or other fields/isotypes.
`RationalRadialStripTrace` concerns a scalar identity; the diagonal result
in `Props.HilbertRankOneTrace` takes a summable rank-one representation as
input. Neither supplies the missing operator bridge.

**Retry:** prove actual continuous descent and identify the joint kernel of
all surviving jets with the weighted theta closure; at degree zero use the
interior jets alone. Independently prove a trace-class factorization or a
trace-norm estimate for the actual quotient operator. With both inputs,
the spans of finitely many whole transpose blocks are finite-dimensional
invariant subspaces of a Hilbert dual, and the increasing orthogonal
projections to such spans converge strongly to identity. Compressing a
trace-class operator by them converges in trace norm (first verify for
finite-rank terms, then approximate in trace norm); the compressed traces
give the finite block sums. This proposed repair needs neither the literal
Fréchet Schauder basis nor norm bounds for oblique coordinate projections.
It is not checked here, and the defects above do not disprove the full
spectral trace identity.

## Reproduce the writer checks

Run `lake build --wfail +Theorems.RationalMellinDivisorJetBlock`. In a fresh
scratch file, ordinarily import this module, then run `#check @Name` and
`#print axioms Name` for the receipt's five fully qualified names with
`lake env lean`. The writer build passed (7449 jobs); each endpoint had
only `propext`, `Classical.choice`, `Quot.sound`. The separate ordinary
client below passed as well: the first example applies the block to an
input with zero jet, the second tests the corrected rank interpretation by
applying the singularity and trace results to the zero test.

```lean
import Theorems.RationalMellinDivisorJetBlock

open Masullo MeasureTheory
open scoped Convolution

example {φ g : ℝ → ℂ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hg : Continuous g) (hcg : HasCompactSupport g) (ρ : criticalStripZetaZeros)
    (hg0 : rationalMellinDivisorJet (compactLogMellin g) ρ = 0) :
    rationalMellinDivisorJet
      (compactLogMellin (φ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g)) ρ = 0 := by
  rw [rationalMellinDivisorJet_convolution hφ hcφ hg hcg ρ, hg0, Matrix.mulVec_zero]

example (ρ : criticalStripZetaZeros) :
    (rationalMellinDivisorJetBlock (0 : ℝ → ℂ) ρ).det = 0 ∧
    Matrix.trace (rationalMellinDivisorJetBlock (0 : ℝ → ℂ) ρ) = 0 := by
  have hz : compactLogMellin (0 : ℝ → ℂ) (shiftedZetaZero ρ) = 0 := by
    simp [compactLogMellin]
  exact ⟨(det_rationalMellinDivisorJetBlock_eq_zero_iff 0 ρ).mpr hz,
    (trace_rationalMellinDivisorJetBlock 0 ρ).trans (by rw [hz, mul_zero])⟩
```

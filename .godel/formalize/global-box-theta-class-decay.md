# Pointwise exponential decay of the global theta function

[Formalize receipt](c64e82e32522f673bc0c0eecefcfb1aed7f21c2579a2f948ea7484441134e9c4-582a453927941b3774d5611a6285568394f99999906c9f6934ff08dd85951500.json) ·
[Lean module](../../Proofs/Theorems/AdeleBoxThetaClassDecay.lean)

Writer base: `a2f09a7a1fc08da97e122ad19cb64890e1d321a8`.
Owning Yah check session: `01a2056e-cbe1-7e70-9b54-64659aeb61ae`.
The campaign handoff records the separate integration and review checks.

## Rendered source and claim

[Masullo, *The Music of the Primes*](../sources/masullo/README.md), 940 pages,
6,756,996 bytes. The local file was checked with `sha256sum`:
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Printed page numbers below equal one-based PDF ordinals. The rendered page
text was read with raster OCR. Formula crops on pp. 12, 83, 84, 92 and 547
were checked in terminal pixel plots from `pdftoppm` grayscale rasters,
separately from extraction (used to navigate or read the surrounding text).

- **§1.1.4, fourth bullet, p. 12:** For an adelic Schwartz–Bruhat test
  \(f\) with \(f(0)=\widehat f(0)=0\), the global theta \(\Phi_F(f)\) is
  said to be exponentially decaying Schwartz–Bruhat on \(C_F\). The
  “i.e.” gloss is \(|\Phi_F(f)(g)|\ll e^{-N|\log |g|_F|}\) for any integer
  \(N\ge 1\) as \(|\log |g|_F|\to\infty\). The preceding bullet's sum is
  over \(F^\times\), not all of \(F\); Definition 2.2.3.1, (2.2.3.1),
  pp. 81–82 uses an idele lift of \(g\in C_F\) and descends the same sum.
- **§1.1.2, p. 11, and Definition D.3.3.1, p. 804:** the all-real-weight
  definition requires \(|\cdot|_F^a\Phi_F(f)\in\mathcal S(C_F)\) for every
  \(a\in\mathbb R\), not just the displayed bound. The stage map is (1.1.2.1),
  p. 11, and the stage definition and maps are (D.3.3.1)–(D.3.3.2), p. 805.
  The full annihilator in Definition D.3.3.3 must be compactly generated,
  not “finitely generated” as in its inductive-limit paragraph: it contains
  the radial dual \(\mathbb R\). Finite generation applies instead to the
  annihilator in the discrete dual of the compact norm-one kernel, as
  explained before Definition D.3.3.1 (see also the
  [radial audit](radial-weighted-frechet.md)).
- **Theorems 2.2.3.2 and 2.2.3.4, pp. 82–86:** (2.2.3.2) on p. 82
  reads \(\Phi_F(f)(g)=|g|_F^{-1}\Phi_F(\widehat f)(g^{-1})
  +|g|_F^{-1}\widehat f(0)-f(0)\). Remark 2.2.3.3 chooses the additive
  Haar measure giving \(\mathbf A_F/F\) volume one with counting measure
  on the diagonal. On p. 83, (2.2.3.4) is the large-norm bound;
  (2.2.3.5) controls the small end *after* subtracting
  \(|g|_F^{-1}\widehat f(0)-f(0)\). The proof uses the inversion equality
  (2.2.3.7) to reduce the latter to the former for \(\widehat f\), then
  combines the ends with the two zero modes absent in (2.2.3.6). The
  large-end proof reduces by linearity to a tensor and takes a common
  lattice on norm-one representatives before applying Schwartz decay.
  Parts (4)–(5) and the argument on pp. 84–86 also concern uniformity
  on bounded families of tests; the fourth bullet only requires the
  constant for each fixed test and exponent, independent of the class.

### Repair of the radial scaling in the printed estimate

Equation (2.2.3.10), p. 84, uses \(\|t_\infty\xi\|=|t|_F\|\xi\|\),
then (2.2.3.11)–(2.2.3.12) use the resulting linear radial growth. The
ordinary Archimedean supremum radius specified on p. 83 takes the square
root of the normalized complex place norm. For the diagonal section
(A.2.2.11) in Definition A.2.2.7 (p. 547), a coordinate at norm \(t\)
is \(t^{1/(N_v(r_1+r_2))}\), with \(N_v=1\) or \(2\). For example, at
an imaginary quadratic field's complex place the ordinary radius scales
by \(\sqrt t\), not \(t\). This invalidates the linear scale argument,
not the claimed decay.

The checked estimate uses the *canonical* section (A.2.2.8)–(A.2.2.9)
and Lemma A.2.2.4 on p. 547 instead. Its ordinary radial scale is
\(t^{1/d}\), with \(d=[K:\mathbb Q]\). A positive power suffices:
use a Schwartz order \(p\ge dN\) also strictly above the lattice rank.

## What Lean supplies

- As in the [accepted global theta handoff](global-box-theta-operator.md)
  at the writer base, `adeleBoxSpan K` is the complex span of
  \(\phi(x_\infty)1_{a+u\widehat{\mathcal O}_K}(x_f)\), where \(\phi\)
  is arbitrary Schwartz on the Euclidean mixed space, \(a\) is a finite
  adele and \(u\) is a finite-adele unit. The finite locally constant compactly
  supported tests are generated mathematically by translated compact open
  boxes, and the source's algebraic tensor presentation gives these global
  generators. No identification with a separately constructed source
  Schwartz–Bruhat LF space and its stages is a Lean input or conclusion.
- In [`AdeleBoxThetaClassDecay`](../../Proofs/Theorems/AdeleBoxThetaClassDecay.lean),
  `adeleBoxThetaLinear_largeNorm_decay` uses the private `box_clearer` to clear the
  whole translated box with a fixed finite denominator (independent of
  the sampled idele), and the coordinate norm comparison and Schwartz
  seminorm to discharge the Archimedean bound. The accepted
  `idele_periodization_rapidDecay_of_support` in
  [`IdeleClassRapidDecay`](../../Proofs/Theorems/IdeleClassRapidDecay.lean)
  chooses a compact cover of the norm-one classes, represents each
  class by a scalar section times a member of that cover, and injects
  the contributing indices into a fixed integer lattice. It uses the
  coordinate lower bound of `exists_infinite_coordinate_ge_scaled_mixedEmbedding`
  with radial factor \(t^{1/d}\) to dominate the absolute sum. The new
  proof then takes the norm of the actual convergent theta series via
  `adeleBoxThetaLinear_apply`, and extends to the full span by linearity.
  The two private input bounds mirror those in the accepted operator module;
  `AdeleBoxThetaOperator.lean` remains byte-identical to the file cited by the
  third-bullet receipt.
- In [`AdeleBoxThetaClassDecay`](../../Proofs/Theorems/AdeleBoxThetaClassDecay.lean),
  `adeleBoxThetaHaar K` is an additive Haar measure calibrated to the
  accepted trace Fourier products on all stages containing the fixed set
  of exceptional places, whose existence follows from
  `exists_finiteCompletionIntegerMass_exceptions` and
  `exists_adeleRestrictedProductHaar` in
  [`AdeleRestrictedProductHaar`](../../Proofs/Theorems/AdeleRestrictedProductHaar.lean).
  This construction supplies the exact normalization hypotheses used in
  the accepted inversion identity; the new proof does not separately
  calculate the mass of the quotient. The new instance gives
  `IsAddHaarMeasure`. The identity `adeleFourier_zero_eq_integral` gives
  the actual trace Fourier zero mode, not a formal or alternative mode:
  the additive character at zero is one. Mathematically, positive
  rescaling of Haar does not affect the condition that this integral vanishes.
- For norm at most one, the private bridge `theta_smallNorm` uses accepted
  `adeleBoxSpan_theta_smallNorm_decay` in
  [`AdeleBoxThetaDecay`](../../Proofs/Theorems/AdeleBoxThetaDecay.lean).
  This theorem uses `adeleBoxSpan_theta_inversion` and the accepted
  absolute Fourier sum estimate with order \(N+1\) to absorb the inverse
  norm factor. Applying it to an idele lift of a class, the two corrections
  are zero by the actual two mode hypotheses; commuting multiplication by a
  principal adele identifies exactly the same series as `adeleBoxThetaLinear_apply`.
  The bound is uniform in the lift, with the idele norm equal to the class norm.
- `adeleBoxThetaLinear_exp_decay` takes the maximum of the two constants
  and rewrites the tails by the sign of the log of the positive class norm.
  It gives one positive constant for *every* class at each exponent, including
  at norm one. It holds for every number field and every natural exponent
  (also zero). Its only analytic premises on the actual span element are
  the two zero modes; neither a Haar calibration nor a support assertion
  remains for the caller. No bounded-family uniformity is claimed.

The zero-mode condition does not force theta to be zero. For instance,
mathematically take the finite indicator of the integer box and an
Archimedean bump with value one at the image of \(1\) and small support
meeting the integer lattice only there. Subtract its translate into a
ball missing the lattice (shrink the support to fit both balls). Neither
ball contains zero, and the two bumps have the same Haar integral.
Thus the two-mode test has theta value one at the identity idele class.
This example is an illustration, not a separate Lean endpoint.

## Full membership remains open in Lean

A bound to arbitrarily high order on the function alone does not imply
Schwartz bounds on derivatives. Even on the radial line,
\(e^{-s^2}\sin(e^{2s^2})\) is smooth and satisfies all such bounds, but the
derivative is unbounded along the positive sequence \(e^{2s^2}=2\pi k\).

The source's **Lemmas 2.2.4.2–2.2.4.3** (pp. 87–91, displays (2.2.4.2)
and (2.2.4.7)) give the ingredients for a different argument: the finite
factor is unchanged by an Archimedean one-parameter subgroup and
its infinitesimal action on the Archimedean Schwartz factor is a linear
vector field; a compact-uniform lattice majorant justifies termwise
differentiation and hence the theta commutation identity.
**Lemma 2.2.4.5(1)**, p. 91 uses the two-mode kernel of (2.2.4.23).
At (2.2.4.31) and the proof immediately following on p. 92, the first
zero mode does vanish after differentiation because multiplication fixes
zero. For the Fourier mode the printed unnumbered calculation following
(2.2.4.31) incorrectly treats the Haar factor as though it were one and
concludes zero for general \(f\). In (2.2.4.29), if \(|\gamma(t)|_F=t^\alpha\), the zero-mode
quotient is \((t^{-\alpha}-1)\widehat f(0)/(t-1)\), so its limit is
\(-\alpha\widehat f(0)\), consistent with (2.2.4.27), p. 91 and the
proof of (2) on p. 95. It vanishes on the required kernel, not in general.

A concrete retry is to construct a common compact open **multiplicative**
finite-idele stabilizer of the finitely many box factors. Locally one can
use units with \((v-1)a\in u\mathcal O\) at exceptional places and use
all integral units elsewhere. Its compact image fixes theta. The remaining
Lie quotient step is to identify the image of the Archimedean units as an
open subgroup of the class quotient by that compact image (the finite
quotient is discrete) and its kernel as a discrete group of integral global
units (discreteness from the Archimedean integer lattice). With the split
radial direction and compact norm-one group, verify the torus and finite
components and the compactly generated annihilator needed by D.3.3.3.
On this *same* quotient, formalize smooth differentiation of theta in all
Lie directions, including commutation with the differentiated box tests
and preservation of the two modes under every iteration. Applying the
present bound to every such test would give the decay of every derivative;
Leibniz with \(e^{as}\), where \(s=\log|g|_F\), and an integer rate above
\(|a|\) would then give the required all-weight seminorms. This is a route,
not a checked membership proof. The rational log-direction result
`hasDerivAt_rationalAdeleClassTheta_logDilation` and the
[radial weighted stage](radial-weighted-frechet.md) do not supply the
general classes, directions, and quotient-stage membership.

## Replay the writer checks

In the candidate workspace:

```sh
lake build --wfail +Theorems.AdeleBoxThetaOperator +Theorems.AdeleBoxThetaClassDecay
scratch=$(mktemp -d)
awk '/^```lean$/{n++; p=1;next} /^```$/{p=0} p{print > (d "/Check" n ".lean")}' \
  d="$scratch" .godel/formalize/global-box-theta-class-decay.md
lake env lean "$scratch/Check1.lean" && lake env lean "$scratch/Check2.lean"
```

The writer build and both separate Lean checks passed. The built decay
signatures quantify only over number fields, actual span elements, natural
exponents and actual idele classes, with the threshold hypothesis on the
large-end result and the two indicated zero modes on the two-ended result.
Every axiom report contains exactly `propext`, `Classical.choice`, `Quot.sound`.
The second block applies the result with arbitrary box centre and scale,
and separately to a span element with an integral-zero input and the same
constant at norm one, through ordinary imports.

```lean
import Theorems.AdeleBoxThetaOperator
import Theorems.AdeleBoxThetaClassDecay
import Theorems.AdeleRestrictedProductHaar

#check @Masullo.adeleBoxThetaLinear_largeNorm_decay
#print axioms Masullo.adeleBoxThetaLinear_largeNorm_decay
#check @Masullo.adeleBoxThetaHaar
#print axioms Masullo.adeleBoxThetaHaar
#check @Masullo.instIsAddHaarMeasure_adeleBoxThetaHaar
#print axioms Masullo.instIsAddHaarMeasure_adeleBoxThetaHaar
#check @Masullo.adeleFourier_zero_eq_integral
#print axioms Masullo.adeleFourier_zero_eq_integral
#check @Masullo.adeleBoxThetaLinear_exp_decay
#print axioms Masullo.adeleBoxThetaLinear_exp_decay
```

```lean
import Theorems.AdeleBoxThetaClassDecay

open IsDedekindDomain Masullo MeasureTheory NumberField
open scoped Classical InnerProductSpace SchwartzMap

variable {K : Type*} [Field K] [NumberField K]
local notation "A" => AdeleRing (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "E" => mixedEmbedding.euclidean.mixedSpace K

private noncomputable def box (φ : 𝓢(E, ℂ)) (a : F) (g : Fˣ) : adeleBoxSpan K :=
  ⟨adeleBoxTensor φ a g, adeleBoxTensor_mem_adeleBoxSpan φ a g⟩

-- No condition on the centre or scale, and no Haar or support obligations.
example (φ : 𝓢(E, ℂ)) (a : F) (g : Fˣ) (N : ℕ)
    (h₀ : adeleBoxTensor φ a g 0 = 0)
    (hF₀ : adeleFourier (adeleBoxThetaHaar K) (adeleBoxTensor φ a g) 0 = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : C,
      ‖adeleBoxThetaLinear (box φ a g) x‖ ≤ R * Real.exp (-(N : ℝ) * |Real.log (ideleClassNorm x)|) :=
  adeleBoxThetaLinear_exp_decay (box φ a g) N h₀ hF₀

-- Integral-zero input for a general span element, and the same constant at norm one.
example (f : adeleBoxSpan K) (N : ℕ) (h₀ : (f : A → ℂ) 0 = 0)
    (hm : ∫ x, (f : A → ℂ) x ∂adeleBoxThetaHaar K = 0) :
    ∃ R : ℝ, 0 < R ∧ (∀ x : C,
      ‖adeleBoxThetaLinear f x‖ ≤ R * Real.exp (-(N : ℝ) * |Real.log (ideleClassNorm x)|)) ∧
      (∀ x : C, ideleClassNorm x = 1 → ‖adeleBoxThetaLinear f x‖ ≤ R) := by
  obtain ⟨R, hR, hb⟩ := adeleBoxThetaLinear_exp_decay f N h₀
    ((adeleFourier_zero_eq_integral _ _).trans hm)
  refine ⟨R, hR, hb, fun x hx ↦ ?_⟩
  simpa only [hx, Real.log_one, abs_zero, mul_zero, Real.exp_zero, mul_one] using hb x
```

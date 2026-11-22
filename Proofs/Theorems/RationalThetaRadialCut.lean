module

public import Theorems.RationalThetaCutClosure
public import Theorems.RationalThetaRadialCore
public import Theorems.RationalIdeleClassHaar

/-! # A forward prime difference after a rational radial cutoff

On the zero line, inserting one new rational finite place has a different
behavior before and after applying an indicator whose log support is bounded
below. After the indicator, the range of the forward difference on the
entire represented two-mode radial theta core is dense in the cut theta
closure. The same identity holds in normalized idele-class `L²` after
multiplying by the square root of the polynomial Sobolev weight.

This is an equality for represented theta images. It does not use or assert
that the indicator of a norm region maps closed subspaces to closed
subspaces, or that the represented core has the manuscript's topological
coinvariant topology.
-/

open Filter NumberField IsDedekindDomain MeasureTheory Set
open scoped Topology

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => RationalIdeleClasses
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "P[" v "]" => ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)
local notation "R" => RationalThetaRadialInput
local notation "LogL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "τ" => fun x : ℝ ↦ rationalIdeleClassLogSection (Multiplicative.ofAdd x)
local notation "Θ[" f "]" => rationalAdeleClassTheta
  (Subtype.val (RationalAdeleSchwartzLF.toUnion (Subtype.val (f : R))))

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

private noncomputable def cutProfile (S : Set ℝ) (s : ℝ) (f : R) : ℝ → ℂ :=
  S.indicator fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) * rationalThetaRadialProfile f x

private theorem cut_theta_ae {S : Set ℝ} (hS : MeasurableSet S) {s : ℝ} (hs : 0 ≤ s) (f : R) :
    ⇑(rationalThetaLogCut hS (rationalThetaRadialWeightedLog le_rfl hs f)) =ᵐ[volume]
      cutProfile S s f :=
  (rationalThetaLogCut_ae hS _).trans ((rationalThetaRadialWeightedLog_ae le_rfl hs f).indicator)

/-- The weighted zero-line map on all represented two-mode radial tests,
followed by a measurable cutoff. -/
public noncomputable def rationalThetaRadialWeightedLogCut {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) : R →+ LogL2 := by
  let F (f : R) := rationalThetaLogCut hS (rationalThetaRadialWeightedLog le_rfl hs f)
  have hadd (f g : R) : F (f + g) = F f + F g := by
    apply Lp.ext
    filter_upwards [cut_theta_ae hS hs (f + g), cut_theta_ae hS hs f, cut_theta_ae hS hs g,
      Lp.coeFn_add (F f) (F g)] with x hfg hf hg hsum
    change F (f + g) x = _ at hfg
    change F f x = _ at hf
    change F g x = _ at hg
    rw [hfg, hsum, Pi.add_apply, hf, hg]
    by_cases hx : x ∈ S <;> simp [cutProfile, hx, mul_add]
  exact { toFun := F, map_add' := hadd, map_zero' := by simpa using hadd 0 0 }

public theorem rationalThetaRadialWeightedLogCut_ae {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) (f : R) :
    ⇑(rationalThetaRadialWeightedLogCut hS hs f) =ᵐ[volume]
      S.indicator (fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) * rationalThetaRadialProfile f x) := by
  unfold rationalThetaRadialWeightedLogCut
  exact cut_theta_ae hS hs f

omit [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)] in
private theorem translated_profile_iterate (d : ℝ) (n : ℕ) (f : R) (x : ℝ) :
    rationalThetaRadialProfile ((rationalThetaRadialInputTranslateAdd d)^[n] f) x =
      rationalThetaRadialProfile f (x + (n : ℝ) * d) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', rationalThetaRadialInputTranslateAdd_apply,
      rationalThetaRadialProfile_translate, ih, Nat.cast_succ]
    congr 1
    ring

/-- Identity minus left translation by the uniformizer, then the zero-line
weight and cutoff. This realizes the difference itself by a radial test. -/
public noncomputable def rationalThetaRadialPrimeDifferenceCut {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) (v : V) (f : R) : LogL2 :=
  rationalThetaRadialWeightedLogCut hS hs
    (f - rationalThetaRadialInputTranslateAdd (Real.log (P[v] : ℝ)) f)

/-- The represented cut difference really is subtraction of the class theta
at the inverse uniformizer translate, restricted to the norm section. -/
public theorem rationalThetaRadialPrimeDifferenceCut_ae {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) (v : V) (f : R) :
    ⇑(rationalThetaRadialPrimeDifferenceCut hS hs v f) =ᵐ[volume]
      S.indicator (fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) *
        (Θ[f] (τ x) - Θ[f] ((QuotientGroup.mk (rationalThetaRadialUniformizer v) : C)⁻¹ * τ x))) := by
  unfold rationalThetaRadialPrimeDifferenceCut
  refine (rationalThetaRadialWeightedLogCut_ae hS hs _).trans ?_
  exact Eventually.of_forall fun _ ↦ congrFun (indicator_congr fun x _ ↦ by
    rw [rationalThetaRadialProfile_sub, rationalThetaRadialInputTranslateAdd_apply,
      rationalThetaRadialProfile_translate, rationalThetaRadialProfile_primeDifference]) _

/-- Closure equality for the full represented radial core, with no restriction
to unramified tensors or restriction on the prime. A measurable cutoff may be
unbounded above, but it must be bounded below in log coordinates. -/
public theorem rationalThetaRadialPrimeDifferenceCut_closure {S : Set ℝ} (hS : MeasurableSet S)
    {a s : ℝ} (ha : S ⊆ Ici a) (hs : 0 ≤ s) (v : V) :
    closure (range (rationalThetaRadialPrimeDifferenceCut hS hs v)) =
    closure (range (rationalThetaRadialWeightedLogCut hS hs)) := by
  unfold rationalThetaRadialPrimeDifferenceCut
  apply closure_range_sub_iterate_eq
  intro f
  have hp : 1 < (P[v] : ℝ) := by exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt
  apply tendsto_zeroLineWeightedLog_cut_translate hs ha (Real.log_pos hp) (rationalThetaRadialProfile f)
    (rationalThetaRadialProfile_log_bound f)
  intro n
  exact (rationalThetaRadialWeightedLogCut_ae hS hs _).trans (Eventually.of_forall fun _ ↦
    congrFun (indicator_congr fun x _ ↦ by rw [translated_profile_iterate]) _)

section ClassHaar

variable [MeasurableSpace C] [BorelSpace C]

local notation "ℓ" => fun g : C ↦ Real.log (ideleClassNorm g)
local notation "ClassL2" => Lp ℂ 2 (rationalIdeleClassHaar : Measure C)

/-- The normalized Haar pullback is isometric on `L²`: the compact fiber
has mass one. -/
public noncomputable def rationalThetaRadialHaarPullback : LogL2 →ₗᵢ[ℂ] ClassL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ ℓ measurePreserving_rationalIdeleClass_logNorm

omit [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)] in
private theorem pullback_ae {u : LogL2} {F : ℝ → ℂ} (hF : ⇑u =ᵐ[volume] F) :
    ⇑(rationalThetaRadialHaarPullback u) =ᵐ[rationalIdeleClassHaar] F ∘ ℓ := by
  unfold rationalThetaRadialHaarPullback
  exact (Lp.coeFn_compMeasurePreserving u measurePreserving_rationalIdeleClass_logNorm).trans
    (measurePreserving_rationalIdeleClass_logNorm.quasiMeasurePreserving.ae_eq_comp hF)

/-- On Haar `L²`, the pullback of the cut vector is cut class theta multiplied
by exactly the square root of the zero-line Sobolev weight. -/
public theorem rationalThetaRadialWeightedLogCut_haar_ae {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) (f : R) :
    ⇑(rationalThetaRadialHaarPullback (rationalThetaRadialWeightedLogCut hS hs f))
        =ᵐ[rationalIdeleClassHaar] (ℓ ⁻¹' S).indicator
          (fun g ↦ (symmetricStripWeightRoot 0 s (ℓ g) : ℂ) * Θ[f] g) := by
  refine (pullback_ae (rationalThetaRadialWeightedLogCut_ae hS hs f)).trans ?_
  exact Eventually.of_forall fun x ↦ by
    have h : Θ[f] = rationalThetaRadialProfile f ∘ ℓ :=
      funext (rationalThetaRadialProfile_class f)
    rw [h]
    exact (indicator_comp_right ℓ).symm

/-- The Haar representative of the cut difference uses the actual idele-class
uniformizer action (without a scalar). -/
public theorem rationalThetaRadialPrimeDifferenceCut_haar_ae {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) (v : V) (f : R) :
    ⇑(rationalThetaRadialHaarPullback (rationalThetaRadialPrimeDifferenceCut hS hs v f))
        =ᵐ[rationalIdeleClassHaar] (ℓ ⁻¹' S).indicator
          (fun g ↦ (symmetricStripWeightRoot 0 s (ℓ g) : ℂ) * (Θ[f] g -
            Θ[f] ((QuotientGroup.mk (rationalThetaRadialUniformizer v) : C)⁻¹ * g))) := by
  refine (pullback_ae (rationalThetaRadialPrimeDifferenceCut_ae hS hs v f)).trans ?_
  exact Eventually.of_forall fun x ↦ by
    simp only [Function.comp_apply]
    by_cases hx : ℓ x ∈ S
    · have hx' : x ∈ ℓ ⁻¹' S := hx
      rw [indicator_of_mem hx, indicator_of_mem hx', rationalThetaRadialProfile_primeDifference,
        rationalThetaRadialProfile_uniformizer, rationalThetaRadialProfile_class f x]
    · have hx' : x ∉ ℓ ⁻¹' S := hx
      rw [indicator_of_notMem hx, indicator_of_notMem hx']

/-- The two closed ranges agree in normalized idele-class Haar `L²`, hence in
the radial zero-line Sobolev norm represented by the weight above. -/
public theorem rationalThetaRadialPrimeDifferenceCut_haar_closure {S : Set ℝ} (hS : MeasurableSet S)
    {a s : ℝ} (ha : S ⊆ Ici a) (hs : 0 ≤ s) (v : V) :
    closure (range (fun f ↦ rationalThetaRadialHaarPullback
      (rationalThetaRadialPrimeDifferenceCut hS hs v f))) =
    closure (range (fun f ↦ rationalThetaRadialHaarPullback
      (rationalThetaRadialWeightedLogCut hS hs f))) := by
  change closure (range (rationalThetaRadialHaarPullback ∘ rationalThetaRadialPrimeDifferenceCut hS hs v)) =
    closure (range (rationalThetaRadialHaarPullback ∘ rationalThetaRadialWeightedLogCut hS hs))
  rw [range_comp, range_comp,
    rationalThetaRadialHaarPullback.isometry.isClosedEmbedding.closure_image_eq,
    rationalThetaRadialHaarPullback.isometry.isClosedEmbedding.closure_image_eq,
    rationalThetaRadialPrimeDifferenceCut_closure hS ha hs v]

end ClassHaar

end Masullo

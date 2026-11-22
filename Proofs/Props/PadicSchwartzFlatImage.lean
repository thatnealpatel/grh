module

public import Lemmas.PadicTestDecomposition
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # The flat, compact-away image in the local Schwartz space

The additive LF topology can be specified using a single fixed finite test
at a time. A finite quotient stage is a finite sum of these assemblies, and
any fixed finite test belongs to a finite quotient stage.
-/

open scoped Padic SchwartzMap
open Function Set Metric

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

@[expose] public def padicSchwartzProfileModule : Submodule ℂ (ℚ_[p] → 𝓢(ℝ, ℂ)) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const _, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.comp_left (smul_zero c)⟩

/-- Additive local Schwartz tests, written as a locally constant finite
variable with compact support and values in the real Schwartz space. -/
@[expose] public def PadicSchwartzProfiles := ↥(padicSchwartzProfileModule p)

local notation "D" => PadicSchwartzProfiles p
local notation "B" => 𝓢(ℝ, ℂ)

public noncomputable instance : AddCommGroup D := inferInstanceAs <|
  AddCommGroup ↥(padicSchwartzProfileModule p)

public noncomputable instance : Module ℂ D := inferInstanceAs <|
  Module ℂ ↥(padicSchwartzProfileModule p)

private abbrev FiniteTest :=
  {h : ℚ_[p] → ℂ // IsLocallyConstant h ∧ HasCompactSupport h}

private noncomputable def assembly (h : FiniteTest p) : B →ₗ[ℂ] D where
  toFun b := ⟨fun y ↦ h.val y • b, h.property.1.comp (· • b),
    h.property.2.comp_left (g := fun c ↦ c • b) (zero_smul ℂ b)⟩
  map_add' b c := Subtype.ext (funext fun y ↦ smul_add (h.val y) b c)
  map_smul' c b := Subtype.ext (funext fun y ↦ smul_comm (h.val y) c b)

private def StageSeminorm := {q : Seminorm ℂ D //
  ∀ h : FiniteTest p, Continuous (q.comp (assembly p h))}

private def stageSeminorms : SeminormFamily ℂ D (StageSeminorm p) := fun q ↦ q.val

/-- The additive locally convex inductive-limit topology. -/
@[no_expose] public noncomputable instance padicSchwartzProfilesTopology : TopologicalSpace D :=
  (stageSeminorms p).moduleFilterBasis.topology

private theorem profiles_withSeminorms : WithSeminorms (stageSeminorms p) := ⟨rfl⟩

private def profileEval (y : ℚ_[p]) : D →ₗ[ℂ] B where
  toFun f := f.val y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem profileEval_apply (y : ℚ_[p]) (f : D) : profileEval p y f = f.val y := rfl

private theorem profileAddTopological : IsTopologicalAddGroup D :=
  (profiles_withSeminorms p).isTopologicalAddGroup

private theorem continuous_profileEval (y : ℚ_[p]) : Continuous (profileEval p y) := by
  let := profileAddTopological p
  apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
  intro i
  refine (profiles_withSeminorms p).continuous_seminorm ⟨_, fun h ↦ ?_⟩
  change Continuous (fun b : B ↦ schwartzSeminormFamily ℂ ℝ ℂ i (h.val y • b))
  exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm i).comp (continuous_const_smul _)

private noncomputable def jetAtZero : ℕ → B →L[ℂ] ℂ
  | 0 => (BoundedContinuousFunction.evalCLM ℂ 0).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
  | j + 1 => (jetAtZero j).comp (SchwartzMap.derivCLM ℂ ℂ)

private theorem jetAtZero_apply (j : ℕ) (b : B) :
    jetAtZero j b = iteratedDeriv j (b : ℝ → ℂ) 0 := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
      rw [jetAtZero, ContinuousLinearMap.comp_apply, ih, iteratedDeriv_succ']
      rfl

/-- The algebraic zero-extension image of the tensor of flat real tests
with compactly supported locally constant tests on the punctured field. -/
public noncomputable def padicSchwartzFlatAwaySpan : Submodule ℂ D :=
  Submodule.span ℂ {f | ∃ (h : FiniteTest p) (b : B),
    h.val 0 = 0 ∧ (∀ j, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) ∧ assembly p h b = f}

private noncomputable def vanishingKernels : Submodule ℂ D :=
  (profileEval p 0).ker ⊓ ⨅ y : ℚ_[p], ⨅ j : ℕ,
    ((jetAtZero j).toLinearMap.comp (profileEval p y)).ker

private theorem mem_vanishingKernels (f : D) : f ∈ vanishingKernels p ↔
    f.val 0 = 0 ∧ ∀ (y : ℚ_[p]) (j : ℕ), iteratedDeriv j (f.val y : ℝ → ℂ) 0 = 0 := by
  simp [vanishingKernels, profileEval_apply, ← jetAtZero_apply]

private noncomputable def ballTest (a : ℚ_[p]) {r : ℝ} (hr : 0 < r) : FiniteTest p :=
  ⟨(closedBall a r).indicator (fun _ ↦ 1),
    (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
      ⟨isClosed_closedBall, IsUltrametricDist.isOpen_closedBall a hr.ne'⟩).isLocallyConstant,
    HasCompactSupport.intro (isCompact_closedBall a r) fun _ hy ↦ indicator_of_notMem hy _⟩

/-- Vanishing on the zero finite slice and flatness on every real slice
characterize the repaired image, already with finite tensor sums. -/
public theorem mem_padicSchwartzFlatAwaySpan_iff {f : D} :
    f ∈ padicSchwartzFlatAwaySpan p ↔
      f.val 0 = 0 ∧ ∀ (y : ℚ_[p]) (j : ℕ), iteratedDeriv j (f.val y : ℝ → ℂ) 0 = 0 := by
  constructor
  · have hle : padicSchwartzFlatAwaySpan p ≤ vanishingKernels p := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, b, h₀, hb, rfl⟩
      change assembly p h b ∈ vanishingKernels p
      rw [mem_vanishingKernels]
      refine ⟨?_, fun y j ↦ ?_⟩
      · change h.val 0 • b = 0
        simp [h₀]
      · rw [← jetAtZero_apply]
        change jetAtZero j (h.val y • b) = 0
        simp [jetAtZero_apply, hb]
    exact fun hf ↦ (mem_vanishingKernels p f).mp (hle hf)
  · rintro ⟨h₀, hf⟩
    obtain ⟨n, s, a, ha, hsum⟩ :=
      padicTest_eq_sum_closedBalls p f.property.1 f.property.2 h₀
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    let r := ((p : ℝ)⁻¹) ^ n
    let h (i : s) := ballTest p (a i) (pow_pos (inv_pos.mpr hp) n)
    have hrep : f = ∑ i : s, assembly p (h i) (f.val (a i)) := by
      apply Subtype.ext
      funext y
      change f.val y = profileEval p y (∑ i : s, assembly p (h i) (f.val (a i)))
      rw [map_sum]
      refine (congrFun hsum y).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
      change (closedBall (a i) r).indicator (fun _ ↦ f.val (a i)) y =
        (closedBall (a i) r).indicator (fun _ ↦ (1 : ℂ)) y • f.val (a i)
      by_cases hy : y ∈ closedBall (a i) r
      · rw [indicator_of_mem hy, indicator_of_mem hy, one_smul]
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_smul]
    rw [hrep]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ⟨h i, f.val (a i), ?_, hf _, rfl⟩
    have hi : (0 : ℚ_[p]) ∉ closedBall (a i) r := by
      rw [mem_closedBall, dist_comm, dist_zero_right]
      exact not_le.mpr (ha i)
    change (closedBall (a i) r).indicator (fun _ ↦ (1 : ℂ)) 0 = 0
    exact indicator_of_notMem hi _

/-- The repaired uncompleted tensor has closed image in the additive LF topology. -/
public theorem isClosed_padicSchwartzFlatAwaySpan :
    IsClosed (↑(padicSchwartzFlatAwaySpan p) : Set D) := by
  have he : (padicSchwartzFlatAwaySpan p : Set D) =
      {f | profileEval p 0 f = 0} ∩ ⋂ (y : ℚ_[p]) (j : ℕ),
        {f | jetAtZero j (profileEval p y f) = 0} := by
    ext f
    simp [mem_padicSchwartzFlatAwaySpan_iff, profileEval_apply, jetAtZero_apply]
  rw [he]
  exact (isClosed_eq (continuous_profileEval p 0) continuous_const).inter
    (isClosed_iInter fun y ↦ isClosed_iInter fun j ↦
      isClosed_eq ((jetAtZero j).continuous.comp (continuous_profileEval p y)) continuous_const)

end Masullo

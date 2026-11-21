module

public import Lemmas.RationalAdeleBoxMajorant
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Joint convergence of rational adelic orbit sums

For the finite box span over ℚ, these are the two-variable convergence and
continuity assertions of Masullo's Lemma 2.2.2.1, pp. 77–80. The summation
omits zero, as in (2.2.2.1).
- There is one summable bound on each compact subset of ideles × adeles.
- Each sample is continuous, giving joint continuity of the sum.
-/

open NumberField Set Topology Filter
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "ι" => algebraMap ℚ A

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J)

local notation "f" => rationalAdeleBoxSum s c b a g

/-- The orbit sum converges uniformly on each compact set of `(idele, adele)` pairs. -/
public theorem tendstoUniformlyOn_rationalAdeleBoxSum_orbit {K : Set (J × A)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t : Finset ℚˣ ↦ fun p ↦ ∑ q ∈ t, rationalAdeleOrbitTerm f q p)
      (fun p ↦ ∑' q, rationalAdeleOrbitTerm f q p) atTop K := by
  obtain ⟨_, hu, hub⟩ := exists_rationalAdeleBoxSum_orbit_majorant s c b a g hK
  exact tendstoUniformlyOn_tsum hu hub

/-- The series of norms also converges uniformly on each compact set. -/
public theorem tendstoUniformlyOn_rationalAdeleBoxSum_orbit_norm {K : Set (J × A)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t : Finset ℚˣ ↦ fun p ↦ ∑ q ∈ t, ‖rationalAdeleOrbitTerm f q p‖)
      (fun p ↦ ∑' q, ‖rationalAdeleOrbitTerm f q p‖) atTop K := by
  obtain ⟨_, hu, hub⟩ := exists_rationalAdeleBoxSum_orbit_majorant s c b a g hK
  exact tendstoUniformlyOn_tsum hu (fun q p hp ↦ by simpa only [norm_norm] using hub q p hp)

/-- The orbit sum is jointly continuous in the dilation and the additive shift. -/
public theorem continuous_rationalAdeleBoxSum_orbit :
    Continuous (fun p ↦ ∑' q, rationalAdeleOrbitTerm f q p) := by
  have hf : Continuous f := continuous_finsetSum s fun i _ ↦
    continuous_const.mul (continuous_rationalAdeleBox (b i) (a i) (g i))
  have hterm (q : ℚˣ) : Continuous (rationalAdeleOrbitTerm f q) :=
    hf.comp
      ((Units.continuous_val.comp continuous_fst).mul (continuous_const.add continuous_snd))
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U, hU, _, hu, hub⟩ := exists_rationalAdeleBoxSum_orbit_local_majorant s c b a g p
  exact ((continuousOn_tsum (fun q ↦ (hterm q).continuousOn) hu hub) p
    (mem_of_mem_nhds hU)).continuousAt hU


private theorem orbit_add_zero_eq_tsum (p : J × A) :
    (∑' q, rationalAdeleOrbitTerm f q p) + f ((p.1 : A) * p.2) =
      ∑' r : ℚ, f ((p.1 : A) * (ι r + p.2)) := by
  let F : ℚ → ℂ := fun r ↦ f ((p.1 : A) * (ι r + p.2))
  let z : Finset ℚ := {0}
  let S : Set ℚ := (z : Set ℚ)ᶜ
  let e : ℚˣ ≃ S := unitsEquivNeZero.trans (Equiv.subtypeEquivRight (fun q ↦ by simp [S, z]))
  obtain ⟨_, hu, hub⟩ := exists_rationalAdeleBoxSum_orbit_majorant s c b a g
    (isCompact_singleton (x := p))
  have hs : Summable (fun q : ℚˣ ↦ F (q : ℚ)) :=
    (hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun q ↦ hub q p (mem_singleton p))).of_norm
  have hf : Summable F := (Finset.summable_compl_iff (s := z)).mp
    (e.summable_iff.mp hs)
  calc
    _ = (∑' r : S, F r) + F 0 := by
      rw [← e.tsum_eq (fun r : S ↦ F r)]
      simp only [F, rationalAdeleOrbitTerm, map_zero, zero_add]
      rfl
    _ = ∑' r, F r := by
      rw [add_comm]
      simpa only [z, Finset.sum_singleton] using hf.sum_add_tsum_compl (s := z)

/-- After adding back the zero term, an additive shift by a principal adele
only permutes the sum. The nonzero sum alone need not be invariant. -/
public theorem rationalAdeleBoxSum_orbit_add_zero_shift (k : J) (x : A) (r : ℚ) :
    (∑' q, rationalAdeleOrbitTerm f q (k, x + ι r)) + f ((k : A) * (x + ι r)) =
      (∑' q, rationalAdeleOrbitTerm f q (k, x)) + f ((k : A) * x) := by
  rw [orbit_add_zero_eq_tsum, orbit_add_zero_eq_tsum]
  simpa only [Equiv.coe_addRight, map_add, add_right_comm, add_assoc] using
    (Equiv.addRight r).tsum_eq (fun q : ℚ ↦ f ((k : A) * (ι q + x)))

end Masullo

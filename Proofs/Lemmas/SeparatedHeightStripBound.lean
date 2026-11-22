module

public import Mathlib.Analysis.Complex.AbsMax

/-! A weighted strip bound from horizontal edges at separated heights. -/

open Complex Set

namespace Masullo

/-- If a polynomially weighted holomorphic function, continuous on the closed strip, is bounded
on its vertical sides and on horizontal segments arbitrarily far above and below, the same bound
holds on the closed strip. -/
public theorem norm_pow_mul_le_on_strip_of_separated_heights {f : ℂ → ℂ}
    {a b : ℝ} (hab : a < b) (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b)) (N : ℕ) {C : ℝ}
    (hvert : ∀ w : ℂ, w.re = a ∨ w.re = b → ‖w ^ N * f w‖ ≤ C)
    (hheight : ∀ R : ℝ, 0 < R →
      ∃ d e : ℝ, d < -R ∧ R < e ∧
        ∀ w : ℂ, a ≤ w.re → w.re ≤ b → w.im = d ∨ w.im = e → ‖w ^ N * f w‖ ≤ C) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖z ^ N * f z‖ ≤ C := by
  intro z haz hzb
  let R := |z.im| + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [abs_nonneg z.im]
  obtain ⟨d, e, hd, he, hhor⟩ := hheight R hR
  have hdz : d < z.im := by
    dsimp [R] at hd
    linarith [neg_abs_le z.im]
  have hze : z.im < e := by
    dsimp [R] at he
    linarith [le_abs_self z.im]
  have hde := hdz.trans hze
  have hp : Differentiable ℂ (fun w : ℂ ↦ w ^ N) := differentiable_id.pow N
  have hg : DiffContOnCl ℂ (fun w : ℂ ↦ w ^ N * f w) (Ioo a b ×ℂ Ioo d e) :=
    hp.diffContOnCl.smul (hf.mono fun _ hw ↦ (mem_reProdIm.mp hw).1)
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo d e)) hg ?_ ?_
  · intro w hw
    rw [Complex.frontier_reProdIm, closure_Ioo hab.ne, closure_Ioo hde.ne,
      frontier_Ioo hab, frontier_Ioo hde] at hw
    rcases hw with h | h
    · obtain ⟨hre, him⟩ := mem_reProdIm.mp h
      exact hhor w hre.1 hre.2 (by simpa only [mem_insert_iff, mem_singleton_iff] using him)
    · exact hvert w (by simpa only [mem_insert_iff, mem_singleton_iff] using (mem_reProdIm.mp h).1)
  · rw [Complex.closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hde.ne]
    exact ⟨⟨haz, hzb⟩, ⟨hdz.le, hze.le⟩⟩

end Masullo

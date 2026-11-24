module

public import Lemmas.DenominatorPairMaskIndex
public import Lemmas.FullRankPrismCount
import Mathlib.Analysis.Convex.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Full-rank bound for the denominator-pair masked prism

Source: Alice, `.godel/alice/denominator-pair-gap-regions.md:3–11,19–25,39–49`
(`e6b43a82`, `1d036a89`), at scan `fa7259d`, unchanged at writer base `fad1c055`.
Owning session: `01a20eab-a304-7e57-9eec-1f7fc75e3637`.

Scope: one fixed ordered denominator pair, mask group and nonzero dyadic bin of `|u|`.
In the full-rank branch `T` is the outer width (the source's `T₁`). The ambient coordinates
are `(m,x,y)`, with `m` the common input, not `F₁*m`. Actual triples are counted via their
injective encoding in those coordinates (source line 7); no reconstruction of second rows
on arbitrary lattice points is asserted. No plane, line, or denominator summation is used.
-/

open Module MeasureTheory Set DenominatorPairMaskIndex

namespace MaskedFullRankPrism

public abbrev Triple := ℤ × ℤ × ℤ
public abbrev Space := Fin 3 → ℝ

/-- The coordinate inclusion `(m,(x,y)) ↦ (m,x,y)` into the real ambient space. -/
@[expose] public def embed : Triple →+ Space where
  toFun p := ![(p.1 : ℝ), (p.2.1 : ℝ), (p.2.2 : ℝ)]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' p r := by ext i; fin_cases i <;> simp

private theorem embed_injective : Function.Injective embed := by
  intro p r h
  apply Prod.ext
  · have h0 : (p.1 : ℝ) = (r.1 : ℝ) := congrFun h 0
    exact_mod_cast h0
  · apply Prod.ext
    · have h1 : (p.2.1 : ℝ) = (r.2.1 : ℝ) := congrFun h 1
      exact_mod_cast h1
    · have h2 : (p.2.2 : ℝ) = (r.2.2 : ℝ) := congrFun h 2
      exact_mod_cast h2

private noncomputable abbrev grid : Submodule ℤ Space := Submodule.span ℤ (range (Pi.basisFun ℝ (Fin 3)))

private theorem grid_eq : grid.toAddSubgroup = AddSubgroup.map embed ⊤ := by
  ext z
  rw [AddSubgroup.mem_map]
  change z ∈ grid ↔ ∃ p : Triple, p ∈ (⊤ : AddSubgroup Triple) ∧ embed p = z
  rw [Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, AddSubgroup.mem_top, true_and]
  constructor
  · intro hz
    obtain ⟨m, hm⟩ := hz 0
    obtain ⟨x, hx⟩ := hz 1
    obtain ⟨y, hy⟩ := hz 2
    refine ⟨(m,x,y), ?_⟩
    ext i
    fin_cases i
    · exact hm
    · exact hx
    · exact hy
  · rintro ⟨p, rfl⟩ i
    fin_cases i
    · exact ⟨p.1, rfl⟩
    · exact ⟨p.2.1, rfl⟩
    · exact ⟨p.2.2, rfl⟩

private abbrev realify (H : AddSubgroup Triple) : Submodule ℤ Space :=
  (H.map embed).toIntSubmodule

private theorem realify_le_grid (H : AddSubgroup Triple) : realify H ≤ grid := by
  change (H.map embed : Set Space) ⊆ (grid.toAddSubgroup : Set Space)
  rw [grid_eq]
  exact AddSubgroup.map_mono le_top

private instance realify_discrete (H : AddSubgroup Triple) : DiscreteTopology (realify H) :=
  DiscreteTopology.of_continuous_injective
    (continuous_subtype_val.subtype_mk (fun z ↦ realify_le_grid H z.property))
    (fun _ _ h ↦ Subtype.ext (congrArg (fun z : grid ↦ (z : Space)) h))

private theorem realify_isZLattice (H : AddSubgroup Triple) (hH : H.index ≠ 0) :
    IsZLattice ℝ (realify H) := by
  refine ⟨?_⟩
  rw [eq_top_iff, ← ZSpan.span_top (Pi.basisFun ℝ (Fin 3))]
  apply Submodule.span_le.mpr
  intro z hz
  change z ∈ grid.toAddSubgroup at hz
  rw [grid_eq] at hz
  obtain ⟨p, -, rfl⟩ := AddSubgroup.mem_map.mp hz
  apply (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.mpr hH : (H.index : ℝ) ≠ 0)).mp
  rw [Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul]
  exact Submodule.subset_span (AddSubgroup.mem_map.mpr ⟨_, H.nsmul_index_mem p, rfl⟩)

private theorem grid_covolume : ZLattice.covolume grid = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain grid volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin 3)) volume),
    ZSpan.fundamentalDomain_pi_basisFun, measureReal_def, volume_pi_pi]
  simp [Real.volume_Ico]

private theorem realify_covolume (H : AddSubgroup Triple) (hH : H.index ≠ 0) :
    ZLattice.covolume (realify H) = (H.index : ℝ) := by
  let _ := realify_isZLattice H hH
  have h := ZLattice.covolume_div_covolume_eq_relIndex (realify H) grid (realify_le_grid H)
  rw [grid_covolume, div_one, grid_eq, AddSubgroup.toIntSubmodule_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective H ⊤ embed_injective,
    AddSubgroup.relIndex_top_right] at h
  exact h

/-- The source's natural number `D`, the index of the mask on the gap pair. -/
@[expose] public def maskIndex (s t l : ℕ) : ℕ := s * t * l / (s.gcd t).gcd l

private theorem maskIndex_pos {s t l : ℕ} (hs : 0 < s) (ht : 0 < t) (hl : 0 < l) :
    0 < maskIndex s t l := by
  apply (Nat.one_le_div_iff (Nat.gcd_pos_of_pos_right _ hl)).mpr
  exact (Nat.gcd_le_right _ hl).trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos hs ht))

/-- The embedded masked triple lattice, without any geometric restrictions. -/
@[expose] public def lattice (d e s t l : ℕ) (F₁ q : ℤ) : Submodule ℤ Space :=
  (AddSubgroup.map embed (maskedLattice d e s t l F₁ q)).toIntSubmodule

public instance (d e s t l : ℕ) (F₁ q : ℤ) : DiscreteTopology (lattice d e s t l F₁ q) :=
  realify_discrete _

/-- Coordinate casting preserves and reflects membership in the actual masked lattice. -/
public theorem embed_mem_lattice_iff {d e s t l : ℕ} {F₁ q : ℤ} {p : Triple} :
    embed p ∈ lattice d e s t l F₁ q ↔ p ∈ maskedLattice d e s t l F₁ q := by
  change embed p ∈ AddSubgroup.map embed (maskedLattice d e s t l F₁ q) ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨r, hr, h⟩
    exact embed_injective h ▸ hr
  · exact fun h ↦ ⟨p, h, rfl⟩

variable {d e s t l : ℕ} {F₁ q : ℤ}

private theorem tripleIndex_ne_zero (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (ht : 0 < t)
    (hl : 0 < l) (hGl : d.gcd e ∣ l) (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1) :
    (maskedLattice d e s t l F₁ q).index ≠ 0 := by
  rw [maskedLattice_index hd he hs ht hl hGl hc]
  exact (Nat.mul_pos (Nat.lcm_pos hd he) (maskIndex_pos hs ht hl)).ne'

/-- In the standard product Lebesgue normalization the embedded mask has covolume `(de/G)D`.
The finite-index bridge uses the index in the full coordinate grid, of covolume one. -/
public theorem lattice_covolume (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (ht : 0 < t)
    (hl : 0 < l) (hGl : d.gcd e ∣ l) (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1) :
    ZLattice.covolume (lattice d e s t l F₁ q) =
      ((d : ℝ) * e / (d.gcd e : ℝ)) * (maskIndex s t l : ℝ) := by
  change ZLattice.covolume (realify (maskedLattice d e s t l F₁ q)) = _
  rw [realify_covolume _ (tripleIndex_ne_zero hd he hs ht hl hGl hc),
    maskedLattice_index hd he hs ht hl hGl hc, Nat.cast_mul]
  congr 1
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_right d he).ne')).mpr
  exact_mod_cast Nat.lcm_mul_gcd d e

/-- Integral coefficients of a linear form on the gap coordinates `(x,y)`. -/
public structure GapForm where
  xCoeff : ℤ
  yCoeff : ℤ

/-- Evaluation on the actual integer gaps. -/
@[expose] public def GapForm.eval (u : GapForm) (x y : ℤ) : ℤ :=
  u.xCoeff * x + u.yCoeff * y

/-- The same form extended to real gap coordinates. -/
@[expose] public def GapForm.evalReal (u : GapForm) (x y : ℝ) : ℝ :=
  (u.xCoeff : ℝ) * x + (u.yCoeff : ℝ) * y

/-- The determinant of the two gap forms in the order `u,w`. -/
@[expose] public def GapForm.det (u w : GapForm) : ℤ :=
  u.xCoeff * w.yCoeff - u.yCoeff * w.xCoeff

private theorem GapForm.eval_cast (u : GapForm) (x y : ℤ) :
    u.evalReal (x : ℝ) (y : ℝ) = (u.eval x y : ℝ) := by
  simp [GapForm.evalReal, GapForm.eval]

private def formMatrix (u w : GapForm) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, (u.xCoeff : ℝ), (u.yCoeff : ℝ); 0, (w.xCoeff : ℝ), (w.yCoeff : ℝ)]

private noncomputable def formMap (u w : GapForm) : Space →ₗ[ℝ] Space :=
  (formMatrix u w).toLin'

private theorem formMap_apply (u w : GapForm) (z : Space) :
    formMap u w z = ![z 0, u.evalReal (z 1) (z 2), w.evalReal (z 1) (z 2)] := by
  rw [formMap, Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp [formMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, GapForm.evalReal]

private theorem formMap_det (u w : GapForm) : LinearMap.det (formMap u w) = (u.det w : ℝ) := by
  rw [← LinearMap.det_toMatrix', formMap, LinearMap.toMatrix'_toLin', Matrix.det_fin_three]
  simp [formMatrix, GapForm.det]

private theorem formMap_det_ne {u w : GapForm} (hdet : u.det w ≠ 0) :
    LinearMap.det (formMap u w) ≠ 0 := by
  rw [formMap_det]
  exact_mod_cast hdet

private noncomputable def radius (u w : GapForm) (V M D T : ℝ) : Space :=
  ![V, 2 * M, |(u.det w : ℝ)| * D * T / M]

/-- The centred outer prism in the original real coordinates, cut out by the common-input
height and the two real extensions of the integral gap forms. -/
public noncomputable def outerPrism (u w : GapForm) (V M D T : ℝ) : Set Space :=
  formMap u w ⁻¹' Icc (-radius u w V M D T) (radius u w V M D T)

/-- Membership uses closed outer faces even though the upper dyadic bound is strict. -/
public theorem mem_outerPrism_iff {u w : GapForm} {V M D T : ℝ} {z : Space} :
    z ∈ outerPrism u w V M D T ↔
      |z 0| ≤ V ∧ |u.evalReal (z 1) (z 2)| ≤ 2 * M ∧
        |w.evalReal (z 1) (z 2)| ≤ |(u.det w : ℝ)| * D * T / M := by
  change ((∀ i, -(radius u w V M D T i) ≤ formMap u w z i) ∧
    (∀ i, formMap u w z i ≤ radius u w V M D T i)) ↔ _
  simp only [← forall_and, ← abs_le, formMap_apply, radius]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

private theorem radius_nonneg {u w : GapForm} {V M D T : ℝ} (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (i : Fin 3) : 0 ≤ radius u w V M D T i := by
  fin_cases i
  · exact hV
  · exact mul_nonneg (by norm_num) hM
  · exact div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hD) hT) hM

private theorem outerPrism_isCompact {u w : GapForm} (hdet : u.det w ≠ 0) (V M D T : ℝ) :
    IsCompact (outerPrism u w V M D T) := by
  let f := ((formMap u w).equivOfDetNeZero (formMap_det_ne hdet)).toContinuousLinearEquiv
  change IsCompact (f.toEquiv ⁻¹' Icc (-radius u w V M D T) (radius u w V M D T))
  rw [← f.toEquiv.image_symm_eq_preimage]
  exact isCompact_Icc.image f.symm.continuous

private theorem outerPrism_convex (u w : GapForm) (V M D T : ℝ) :
    Convex ℝ (outerPrism u w V M D T) := (convex_Icc _ _).linear_preimage _

private theorem outerPrism_zero {u w : GapForm} {V M D T : ℝ} (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hD : 0 ≤ D) (hT : 0 ≤ T) : 0 ∈ outerPrism u w V M D T := by
  simp only [mem_outerPrism_iff, Pi.zero_apply, GapForm.evalReal, mul_zero, add_zero, abs_zero]
  exact ⟨radius_nonneg (u := u) (w := w) hV hM hD hT 0,
    radius_nonneg (u := u) (w := w) hV hM hD hT 1,
    radius_nonneg (u := u) (w := w) hV hM hD hT 2⟩

/-- The outer prism has volume `16*V*D*T` in `(m,x,y)` coordinates. The change to
`(m,u,w)` multiplies volume by the absolute determinant of the gap forms. -/
public theorem outerPrism_volume {u w : GapForm} (hdet : u.det w ≠ 0) {V M D T : ℝ}
    (hV : 0 < V) (hM : 0 < M) (hD : 0 < D) (hT : 0 < T) :
    volume.real (outerPrism u w V M D T) = 16 * V * D * T := by
  let r := radius u w V M D T
  have hr i : 0 ≤ r i := radius_nonneg hV.le hM.le hD.le hT.le i
  change volume.real (formMap u w ⁻¹' Icc (-r) r) = _
  rw [measureReal_def, Measure.addHaar_preimage_linearMap volume (formMap_det_ne hdet),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), formMap_det, Real.volume_Icc_pi,
    ENNReal.toReal_prod]
  simp only [Pi.neg_apply, sub_neg_eq_add, ENNReal.toReal_ofReal (add_nonneg (hr _) (hr _)),
    Fin.prod_univ_three, abs_inv]
  change |(u.det w : ℝ)|⁻¹ * ((V + V) * (2 * M + 2 * M) *
    (|(u.det w : ℝ)| * D * T / M + |(u.det w : ℝ)| * D * T / M)) = _
  have hδ : |(u.det w : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hdet)
  field_simp
  ring

/-- Necessary conditions on each actual passing triple. The source's first-row identities give
`row_d` and `row_e`; extra smoothness, raw gap or second-row restrictions can only shrink the
family. The bin and product condition are tested on the original integral forms. -/
public structure Passes (d e s t l : ℕ) (F₁ q : ℤ) (u w : GapForm) (V M T : ℝ)
    (p : Triple) : Prop where
  m_pos : 0 < p.1
  m_le : (p.1 : ℝ) ≤ V
  mask_x : (s : ℤ) ∣ p.2.1
  mask_y : (t : ℤ) ∣ p.2.2
  mask_diff : (l : ℤ) ∣ p.2.1 - p.2.2
  row_d : (d : ℤ) ∣ F₁ * p.1 - q * p.2.1
  row_e : (e : ℤ) ∣ F₁ * p.1 - q * p.2.2
  bin_lo : M ≤ |(u.eval p.2.1 p.2.2 : ℝ)|
  bin_hi : |(u.eval p.2.1 p.2.2 : ℝ)| < 2 * M
  product_le : |(u.eval p.2.1 p.2.2 : ℝ) * (w.eval p.2.1 p.2.2 : ℝ)| ≤
    |(u.det w : ℝ)| * (maskIndex s t l : ℝ) * T

/-- Passing triples lie in the closed outer prism and in the embedded mask lattice. -/
public theorem passing_mem {u w : GapForm} {V M T : ℝ} {p : Triple} (hM : 0 < M)
    (hp : Passes d e s t l F₁ q u w V M T p) :
    embed p ∈ outerPrism u w V M (maskIndex s t l) T ∩ (lattice d e s t l F₁ q : Set Space) := by
  refine ⟨?_, embed_mem_lattice_iff.mpr ?_⟩
  · rw [mem_outerPrism_iff]
    change |(p.1 : ℝ)| ≤ V ∧ |u.evalReal (p.2.1 : ℝ) (p.2.2 : ℝ)| ≤ 2 * M ∧
      |w.evalReal (p.2.1 : ℝ) (p.2.2 : ℝ)| ≤ |(u.det w : ℝ)| * (maskIndex s t l : ℝ) * T / M
    rw [u.eval_cast, w.eval_cast, abs_of_pos (Int.cast_pos.mpr hp.m_pos)]
    refine ⟨hp.m_le, hp.bin_hi.le, (le_div_iff₀ hM).mpr ?_⟩
    have hprod := hp.product_le
    rw [abs_mul] at hprod
    exact (mul_le_mul_of_nonneg_left hp.bin_lo (abs_nonneg _)).trans
      (by simpa only [mul_comm] using hprod)
  · exact mem_maskedLattice.mpr
      ⟨mem_gapMask.mpr ⟨hp.mask_x, hp.mask_y, hp.mask_diff⟩, hp.row_d, hp.row_e⟩

/-- For one full-rank outer bin, the number of distinct actual passing triples is at most
`1024*V*G*T/(d*e)`. The family is injectively encoded by `(m,x,y)`. The rank witnesses need
only lie in the outer prism and the masked lattice, not in the family of passing triples. -/
public theorem passing_card_le {α : Type*} [Fintype α] (coords : α ↪ Triple)
    (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (ht : 0 < t) (hl : 0 < l)
    (hGl : d.gcd e ∣ l) (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1)
    {u w : GapForm} (hdet : u.det w ≠ 0) {V M T : ℝ} (hV : 0 < V) (hM : 0 < M) (hT : 0 < T)
    (hpass : ∀ a, Passes d e s t l F₁ q u w V M T (coords a))
    (v : Fin 3 → Triple) (hv : LinearIndependent ℝ (fun i ↦ embed (v i)))
    (hvL : ∀ i, v i ∈ maskedLattice d e s t l F₁ q)
    (hvK : ∀ i, embed (v i) ∈ outerPrism u w V M (maskIndex s t l) T) :
    (Fintype.card α : ℝ) ≤ 1024 * V * (d.gcd e : ℝ) * T / ((d : ℝ) * e) := by
  let L := lattice d e s t l F₁ q
  let K := outerPrism u w V M (maskIndex s t l) T
  let _ : IsZLattice ℝ L := realify_isZLattice _ (tripleIndex_ne_zero hd he hs ht hl hGl hc)
  have hD : (0 : ℝ) < (maskIndex s t l : ℝ) := Nat.cast_pos.mpr (maskIndex_pos hs ht hl)
  have hG : (0 : ℝ) < (d.gcd e : ℝ) := Nat.cast_pos.mpr (Nat.gcd_pos_of_pos_right d he)
  have hde : (0 : ℝ) < (d : ℝ) * e := mul_pos (Nat.cast_pos.mpr hd) (Nat.cast_pos.mpr he)
  have hcompact : IsCompact K := outerPrism_isCompact hdet V M _ T
  have hbound := FullRankPrismCount.prism_card_le L hcompact (outerPrism_convex u w V M _ T)
    (outerPrism_zero hV.le hM.le hD.le hT.le) hv (fun i ↦ embed_mem_lattice_iff.mpr (hvL i)) hvK
    hG hD hde (outerPrism_volume hdet hV hM hD hT) (lattice_covolume hd he hs ht hl hGl hc)
  let S := K ∩ (L : Set Space)
  have hS : S.Finite := (ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin 3)) hcompact.isBounded).subset
    (fun _ hz ↦ ⟨hz.1, realify_le_grid _ hz.2⟩)
  let _ := hS.fintype
  let f (a : α) : S := ⟨embed (coords a), passing_mem hM (hpass a)⟩
  have hf : Function.Injective f := fun _ _ h ↦ coords.injective (embed_injective (congrArg Subtype.val h))
  have hcard : Fintype.card α ≤ Nat.card S := by
    rw [← Nat.card_eq_fintype_card (α := α)]
    exact Nat.card_le_card_of_injective f hf
  exact (Nat.cast_le.mpr hcard).trans hbound

end MaskedFullRankPrism

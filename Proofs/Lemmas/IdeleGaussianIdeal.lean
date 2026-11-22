module

public import Theorems.IdeleIdealClass

/-! # The finite ideal supporting the Gaussian at an idele -/

open NumberField
open scoped nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- The finite integrality test at `g` uses the inverse of its finite ideal. -/
@[expose] public noncomputable def ideleGaussianIdeal (g : IdeleGroup (𝓞 K) K) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (finiteIdeleIdeal K (ideleFinitePart g))⁻¹

end Masullo

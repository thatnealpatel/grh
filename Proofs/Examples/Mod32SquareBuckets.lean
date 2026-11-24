module

public import Mathlib.Data.ZMod.Basic

/-!
# Where the odd prime squares land

These finite calculations look *backwards* through the squaring map. The
four inputs in each row explain the factor `4/16` when the progression PNT
is applied. Equal fiber sizes by themselves say nothing about prime counts.
-/

namespace PrimeSquareRamp

private def roots (b : ZMod 32) : Finset (ZMod 32) :=
  Finset.univ.filter fun r => r ^ 2 = b

example : roots 1 = {1, 15, 17, 31} := by decide
example : roots 9 = {3, 13, 19, 29} := by decide
example : roots 17 = {7, 9, 23, 25} := by decide
example : roots 25 = {5, 11, 21, 27} := by decide

/-- The finer labels are invisible to the mod-four square sign. -/
example (r : ZMod 32) (hr : r.val % 2 = 1) : (r ^ 2).val % 4 = 1 := by
  revert r
  decide

end PrimeSquareRamp

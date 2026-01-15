import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

--Here we prove some basic facts show how the existence quantifier works
theorem exists_sq_eq_neg_x : ∃ x : ℝ, x^2 = -x := by
  use 0
  norm_num

theorem exists_sq_eq_neg_x_2 : ∃ x : ℝ, x^2 = -x := by
  use -1
  norm_num

theorem exists_int_rem_two_three_div_five_six : ∃ x : ℤ, x % 5 = 2 ∧ x % 6 = 3 := by 
  use 27
  constructor --for verbosity, splits both sides into cases
  · norm_num    --auto arithmetic
  · norm_num    --auto arithmetic





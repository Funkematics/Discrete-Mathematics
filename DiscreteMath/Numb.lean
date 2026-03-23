import Mathlib



theorem sum_eq (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with 
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith


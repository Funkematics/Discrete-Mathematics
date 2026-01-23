import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic

variable (a b c : Finset ℕ)

section
variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end

def mul_inbetween (n m k : ℤ) : ℤ :=
  ⌊n/k⌋ - ⌊(m-1)/k⌋ 

#eval mul_inbetween 3400 (-600) 10

variable {α : Type*}
variable (s t u : Set α)
open Set

theorem subsetcap (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def]
  rw [inter_def]
  rw [inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩ 
  exact ⟨h _ xs, xu⟩  

theorem subsetcap2 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩ 

theorem subsetcup (h : s ⊆ t) : s ∪ u ⊆ t ∪ u := by
  rw [subset_def]
  rw [union_def]
  rw [union_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  intro x hx
  cases hx with
    | inl xs => left; exact h _ xs
    | inr xu => right; exact xu




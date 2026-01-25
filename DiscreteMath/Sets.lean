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

--The function finds cardinalty of a subset defined by divisibility by k of a larger integer subset of range n to k, ie it finds the number of elements divisibly by k in range [n,k]--

def mul_inbetween (n m k : ℤ) : ℤ :=
  ⌊n/k⌋ - ⌊(m-1)/k⌋ 

#eval mul_inbetween 3400 (-600) 10

variable {α : Type*}
variable (s t u : Set α)
open Set

-- Below are 4 ways of proving the exact same theorem --

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

theorem subsetcap3 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩ 

theorem subsetcap4 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := 
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩


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

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2  --hx.1 and hx.2 ≃ hx.left and hx.right
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩ 



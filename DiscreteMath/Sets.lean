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

-- Finds cardinality of elements divisible by k in range [m,n]

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

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by 
  rintro x ⟨xs, xt | xu⟩ --This ended up creating two cases
  · left
    exact ⟨xs, xt⟩ 
  · right
    exact ⟨xs, xu⟩ 

theorem rev_examp : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with ⟨xs, xt⟩ | ⟨xs, xu⟩ 
  · exact ⟨ xs, Or.inl xt⟩
  · exact ⟨ xs, Or.inr xu⟩ 


theorem trans1 (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
 have h4 : x ∈ B := h1 h3   --Proof that x ∈ B
 exact h2 h4                --x ∈ C because B ⊆ C and x ∈ B

theorem imp {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
 intro h3
 have h4 : x ∈ B := h1 h3
 exact h2 h4


theorem subset.reflex (A : Set U) : A ⊆ A := by
  intro x
  intro h
  exact h

theorem subset.trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x
  intro h
  have h3 : x ∈ B := h1 h
  exact h2 h3

--Facts involving compliments below, adapted from Set Theory game


example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  intro h3                            --Suppose A ⊆ B, x ∈ A and x ∉ B
  have h4 : x ∈ B := h3 h1            --Then x ∈ B from x ∈ A
  exact h2 h4                         --Leads to contradiction since have x ∈ B and x ∉ B

theorem mem.compl.iff (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
    rfl       --demonstration that x ∈ Aᶜ and x ∉ A are equivalent

theorem compl.subset.compl.of.subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h2
  rw [mem.compl.iff A x]
  rw [mem.compl.iff B x] at h2
  by_contra h
  have h3 : x ∈ B := h1 h
  exact h2 h3

theorem compl.compl (A : Set U) : Aᶜᶜ = A := by
  apply Subset.antisymm
  · intro x h1
    rw [mem.compl.iff] at h1
    rw [mem.compl.iff] at h1
    push_neg at h1
    exact h1
  · intro x h1
    rw [mem.compl.iff]
    rw [mem.compl.iff]
    push_neg
    exact h1

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  · intro h1
    exact compl.subset.compl.of.subset h1
  · intro h1
    apply compl.subset.compl.of.subset at h1
    rw [compl.compl] at h1
    rw [compl.compl] at h1
    exact h1


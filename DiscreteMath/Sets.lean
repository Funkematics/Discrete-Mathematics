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



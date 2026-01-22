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

#eval mul_inbetween 100000 10000 10
#eval mul_inbetween 3400 (-600) 10
#eval mul_inbetween 73 -73 2

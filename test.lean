import Lean

variable (A B C : Prop)

#check A ∧ ¬B → C

#check λ x: Nat => x + 5
#eval (λ x : Nat => x + 5) 10
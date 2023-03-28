import Mathlib.Init.Set
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Order


variable(a b Q : Type)

def DownwardsClosed (d : Set ℚ) : Prop :=
  ∀ r r' : ℚ, ((r'∈ d) ∧ (r < r')) → (r ∈ d)  

  -- Set.univ (for dedekind cut instead of T)
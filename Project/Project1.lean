import Mathlib.Init.Set
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Order


variable(a b Q : Type)

def DownwardsClosed (d : Set ℚ) : Prop :=
  ∀ r r' : ℚ, ((r'∈ d) ∧ (r < r')) → (r ∈ d)  

  -- Set.univ (for dedekind cut instead of T)

def DedekindCut(d : Set ℚ) : Prop :=
  DownwardsClosed(d) ∧ d ≠ ∅ ∧ d ≠ Set.univ

def Real : Type :=
  {x : Set ℚ // DedekindCut(x)}

def IsUpperBound(S : Set) (n : Real) : Prop :=
  ∀ x : Real, (x ∈ S) → (n >= x)

def IsLUB (S : Set) (n : Real) : Prop :=
  ∀ x : Real, ((IsUpperBound S x) → n <= x) ∧ IsUpperBound S n

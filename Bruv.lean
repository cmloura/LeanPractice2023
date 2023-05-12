import Mathlib.Init.Set
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Order

variable(a b Q : Type)

def DownwardsClosed (d : Set ℚ) : Prop :=
  ∀ r r' : ℚ, ((r'∈ d) ∧ (r < r')) → (r ∈ d)  

    -- Set.univ (for dedekind cut instead of T)

def DedekindCut(d : Set ℚ) : Prop := DownwardsClosed d ∧ d ≠ ∅ ∧ d ≠ Set.univ

abbrev Real : Type := {x : Set ℚ // DedekindCut x }

instance : LE Real where
  le := λr₁ r₂ : Real => r₁.val ⊆ r₂.val

lemma unbounded : ∀r : Real, ∃s: Real, r < s := by
  intros i
  let T := { q : ℚ | ∃q' : ℚ, q' ∈ i.val ∧ q = q' + 1 }
  have l₁ : i.val ⊆ T := by
    intro x h₁
    have l₂ : x - 1 < x := by simp
    have l₃ : x - 1 ∈ i.val := i.property.left (x-1) x ⟨h₁,l₂⟩
    have l₄ : x = (x - 1) + 1 := by simp
    exact ⟨x - 1, l₃, l₄⟩
  have l₂ : i.val ≠ T := sorry
  have l₃ : DownwardsClosed T := sorry
  have l₄ : T ≠ ∅ := by
    apply (Set.nonempty_iff_ne_empty).mp
    have k₁ : ∀x : ℚ, x ∈ i.val → x ∈ T := l₁
    have k₂ : j - 1 ∈ i.val := l₃
    have k3 : (j-1) ∈ i.val → (j-1) ∈ T := k₁ k₂
    have k4 : (j-1) ∈ T := k3 k₂
    have k5 : Set.isNonempty T := ⟨j-1, k4⟩
    exact k5
    
  have l₅ : T ≠ Set.univ := sorry

def IsUpperBound(S : Set Real) (n : Real) : Prop := ∀ x : Real, (x ∈ S) → (n >= x)

def IsLUB (S : Set Real) (n : Real) : Prop :=
  ∀ x : Real, ((IsUpperBound S x) → n <= x) ∧ IsUpperBound S n

theorem bigTheorem : ∀S : Set Real, (S ≠ ∅  ∧ ∃r : Real, IsUpperBound S r) 
  → ∃l : Real, IsLUB S l := by
  intros S h₁
  have ⟨h₂,r,h₃⟩ := h₁
  clear h₁
  let l := { r : ℚ | ∃s : Real, s ∈ S ∧ r ∈ s.val }
  have l₁ : DedekindCut l := by
     have lemma₁ : l ≠ Set.univ := by
        apply (Set.ne_univ_iff_exists_not_mem l).mpr
        have ⟨s,h₃⟩ := unbounded r
        sorry
     have lemma₂ : l ≠ ∅ := by
        apply (Set.nonempty_iff_ne_empty).mp
        have ⟨⟨elt, h₃⟩,h₂⟩ := Set.nonempty_iff_ne_empty.mpr h₂
        have h₄ := h₃.right.left
        have ⟨elt',h₅⟩ := Set.nonempty_iff_ne_empty.mpr h₄
        have h₆ : elt' ∈ l := ⟨⟨elt,h₃⟩,⟨h₂,h₅⟩⟩
        exact ⟨elt',h₆⟩
     have lemma₃ : DownwardsClosed l := by
        intros r r' h₃
        have ⟨h₄,h₅⟩ := h₃
        sorry
  have r₂ : Real := ⟨l, l₁⟩
  refine ⟨r₂, ?_⟩
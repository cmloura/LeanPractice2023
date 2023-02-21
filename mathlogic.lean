--variable (α : ℕ) (b c d a e x: ℕ)

--variable(hab : a = b) (hcb : c = b) (hcd : c = d)

--example : a = d :=

--Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

--theorem T : a = e :=
 -- calc
   -- a = b     := h1
 --   _ = c + 1 := h2
 --   _ = d + 1 := congrArg Nat.succ h3
 --   _ = 1 + d := Nat.add_comm d 1
  --  _ = e     := Eq.symm h4


example : ∃ x : Nat , x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩ 

-- ∀x ∈ ℕ, 0 * x = x * 0 = 0  

example : ∀ x : Nat, x * 0 = 0 :=  
  λ(a1 : Nat) =>
    rfl

-- ∀x ∈ ℕ, 0 * x = 0  
example : ∀ x : Nat, 0 * x = 0 :=
  λ(a1 : Nat) => 
    Nat.recOn a1 (rfl : 0 * 0 = 0) (λ(n : Nat) => 
      λ(h1 : 0 * n = 0) => by
        calc
          0 * (n+1) = (0 * n) + 0 := rfl
          _ = 0 + 0               := by rw[h1]
          _ = 0                   := rfl
        )

-- 

def ChrisSum (p : Nat) : Nat :=
  match p with
    | 0 => 0
    | n + 1 => ChrisSum n + (n+1)

-- ChrisSum n = n * (n+1)/2

example : ∀ x : Nat, ChrisSum x = x * (x+1) / 2 :=
  λ(a : Nat) =>
    Nat.recOn a (rfl) (λ(n : Nat) =>
      λ(h1 : ChrisSum n = n * (n+1) / 2) =>
        calc
          ChrisSum (n+1) = ChrisSum n + (n+1)   := rfl
          _ = (n * (n+1) / 2) + (n+1)           := by rw[h1]
          _ = (n+1) * (n/2 + 1)                 := by rw[<-Nat.left_distrib]
    ) 
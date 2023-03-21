def GrahamSum (p : Nat) : Nat :=
  match p with 
    | 0 => 0
    | n + 1 => GrahamSum n + (2*(n+1)-1)

example : ∀ x : Nat, GrahamSum x = x*x :=
  λ(a : Nat) =>
    Nat.recOn a (rfl) (λ(n : Nat) =>
      λ(h1 : GrahamSum n = n*n) =>
        calc
          GrahamSum (n+1) = GrahamSum n + 2*(n+1) - 1              := rfl
          _ = (n * n) + 2*n + 2 - 1                                := by simp[*, Nat.left_distrib, Nat.add_assoc]
          _ = (n * n) + 2*n + 1                                    := rfl
          _ = (n + 1)*(n + 1)                                      := by simp[Nat.add_assoc, Nat.mul_comm, <-Nat.left_distrib, Nat.left_distrib, <-Nat.right_distrib]
    )


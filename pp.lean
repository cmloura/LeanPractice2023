def MT {p : Prop} {q : Prop}: (((p -> q) ∧ ¬q) -> ¬p) :=
  fun h1 : ((p -> q) ∧ ¬q) => 
    (fun (h2 : p) => h1.right (h1.left h2))

--∀x(F(x) → G(x)), ∃x(H(x) ∧ ¬G(x)) ⊢ ∃x(H(x) ∧ ¬F(x))

variable(F G H : ℕ → Prop  )
variable(x y : ℕ )
variable(a b : Prop )


example (h1 : ∀ x : ℕ, F x → G x ) (h2 : ∃ x : ℕ, H x ∧ ¬G x ) 
  : ∃ x : ℕ, (H x ∧ ¬ F x) :=
have ⟨a,(ha: H a ∧ ¬G a)⟩ := h2
have proofnotfa := MT $ And.intro (h1 a) ha.right
⟨a, And.intro ha.left proofnotfa⟩ 


-- ∃x(F(x) ∧ ¬G(x)), ∀x(F(x) → H(x)) ⊢ ∃x(H(x) ∧ ¬G(x))

example (h1 : ∃ x : ℕ, F x ∧ ¬ G x) (h2 : ∀ x : ℕ, F x → H x)
  : ∃ x : ℕ, H x ∧ ¬G x :=

  have ⟨a, (ha: F a ∧ ¬G a )⟩ := h1
  have proofha := (h2 a) ha.left
  ⟨a, And.intro proofha ha.right⟩  

  --∀x(F(x) → G(x)), ¬∃x(G(x) ∧ H(x)) ⊢ ¬∃x(H(x) ∧ F(x))

  example (h1 : ∀x : ℕ, F x → G x) (h2 : ¬∃ x : ℕ, G x ∧ H x)
    : ¬∃x : ℕ, H x ∧ F x :=
  fun (a1 : ∃x : ℕ, H x ∧ F x) => 
    have ⟨a, (ha: H a ∧ F a)⟩ := a1  
    h2 ⟨a, And.intro ((h1 a) ha.right) ha.left ⟩ 


-- ¬∃x(F(x) ∧ G(x)), ∃x(H(x) ∧ F(x)) ⊢ ∃x(H(x) ∧ ¬G(x))
example (h1 : ¬∃ x : ℕ, F x ∧ G x) (h2 : ∃ x : ℕ, H x ∧ F x)
  : ∃ x : ℕ, H x ∧ ¬G x :=
have ⟨a, (ha: H a ∧ F a )⟩ := h2
have proofnga := λ(ga : G a) => h1 ⟨a, And.intro ha.right ga⟩ 
⟨a, And.intro ha.left proofnga⟩

-- !(a v b) |- !a ^ !b
example (h1 : ¬(a ∨ b)) : ¬a ∧ ¬b :=

have proofna := λ(a1 : a) => h1 $ Or.intro_left b a1
have proofnb := λ(a2 : b) => h1 $ Or.intro_right a a2

And.intro proofna proofnb

axiom DNE {p : Prop} : ¬¬p -> p

-- !(a ^ b) |- !a v !b
example(h1 : ¬(a ∧ b)) : ¬a ∨ ¬b :=
DNE λ(a1 : ¬(¬a ∨ ¬b)) => 
  have proofa := λ(a2 : ¬a) =>
    a1 $ Or.intro_left (¬b) a2
  have proofb := λ(a3 : ¬b) =>
    a1 $ Or.intro_right (¬a) a3
  h1 $ And.intro (DNE proofa) (DNE proofb)





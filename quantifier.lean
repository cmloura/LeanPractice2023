-- ∀x(F(x) ∧ G(x)) ⊢ F(c)

variable(F G : ℕ → Prop)
variable(b c d : ℕ)

example (h1 : ∀ x : ℕ, F x ∧ G x): F c :=
  (h1 $ c).left


-- ∀xF(x), (F(c) → G(c)) ⊢ G(c)
example (h1 : ∀ x : ℕ, F x) (h2 : F c → G c) : G c :=
  h2 $ (h1 $ c)

-- ∀x∀y(F(x) → G(y)), F(c) ⊢ G(d)
example (h1 : ∀ x : ℕ, ∀ y : ℕ, F x → G y) (h2 : F c) : G d :=
  ((h1 $ c) $ d) $ h2

-- ∀x∀y(F(x) ↔ G(y)), F(c) ⊢ F(d)
example (h1 : ∀ x y : ℕ, F x ↔ G y) (h2 : F c) : G d :=
  ((h1 $ c) $ d).mp $ h2


-- ∀xF(x), ((F(b) ∧ F(c)) → G(c)) ⊢ ∃xG(x)
example (h1 : ∀ x : ℕ,  F x) (h2 :(F b ∧ F c) → G c) : ∃ x : ℕ, G x :=
 ⟨ c, (h2 $ (And.intro (h1 $ b) (h1 $ c))) ⟩ 

 -- |- ∀x (F(x) -> Ey F(y))
 example : ∀ x: ℕ, F x → ∃ y : ℕ,  F y := 
  fun x : ℕ => (fun h1 : F x => ⟨x, h1⟩)

-- ∀x(F(x) → G(x)), ∀xF(x) ⊢ ∀xG(x)

example (h1 : ∀ x : ℕ, F x → G x) (h2: ∀ x : ℕ, F x) : ∀ x : ℕ, G x :=
  fun x : ℕ => (h1 $ x) $ (h2 $ x)

-- ∀x¬F(x), F(d) ⊢ ¬∀xF(x)
example (h1 : ∀ x : ℕ, ¬F x) (h2 : F d) : ¬∀ x : ℕ , F x :=
  ((h1 $ d) $ h2).elim -- EFQ rule

-- ¬∃xF(x) ⊢ ∀x¬F(x)
example (h1 : ¬∃ x : ℕ, F x) : ∀ x : ℕ, ¬F x :=
  fun a : ℕ => (fun fa : F a => h1 $ ⟨a, fa⟩)
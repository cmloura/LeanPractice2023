-- variable (p q : Prop) 

--variable (h : p ∧ ¬ q)

--#check And.intro (And.right) (And.left)


--variable(A B C D: Prop)
--variable(h1 : A → (B → C))
--variable(h2 : D → A)
--variable(h3 : D)
--variable(h4 : B)

--#check h2 h3
--#check h1 (h2 h3)
--#check (h1 (h2 h3)) h4 


variable(A : Prop)

theorem test(p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := 
  by apply And.intro
      exact hp
      apply And.intro
      exact hq
      exact hp

variable(p q r : Prop)

example (h1 : P) : P := h1

example (h1 : P) (h2 : P → (P → Q)) : Q := ((h2 h1) h1)

-- P, Q, (P → (Q → R)) ⊢ R

example (h1 : p) (h2 : q) (h3 : p -> (q -> r)) : r := 
  (h3 h1) h2

example : p -> p :=
  fun h1 => (h1 : p)

-- Q ⊢ (P → Q)

example (h1 : q) : p -> q :=
  fun _ => h1

-- (P → Q), (Q → R) ⊢ (P → R)

example (h1 : p -> q) (h2 : q -> r) : p -> r := 
  fun h3 => h2 (h1 h3)

-- The function goes on the left and the argument on the right

-- P, (¬Q → ¬P) ⊢ Q

def DNI {p : Prop} : p -> ¬¬p :=
  fun h1 : p => (fun h2 : ¬p => h2 h1)

def MT {p : Prop} {q : Prop}: (((p -> q) ∧ ¬q) -> ¬p) :=
  fun h1 : ((p -> q) ∧ ¬q) => 
    (fun (h2 : p) => h1.right (h1.left h2))

example (h1 : p) (h2 : ¬q -> ¬p) : ¬¬q  :=
  fun (h3 : ¬q) => (h2 h3) h1



-------------------------------------------------------------

axiom DNE {p : Prop} : ¬¬p -> p 

example (h1 : p) (h2 : ¬q -> ¬p) : q  :=
  DNE (fun (h3 : ¬q) => (h2 h3) h1)

-- ¬P, (¬Q → P) ⊢ Q
example (h1 : ¬p) (h2 : ¬q -> p) : q :=
  DNE $ MT $ And.intro h2 h1 ----------------------- Different syntax instead of ()


-- (P ∧ Q) ⊢ (P ∨ Q)
example (h1: p ∧ q) : p ∨ q :=
  Or.inl $ h1.left

-- ¬P, ¬Q ⊢ ¬(P ∨ Q)
example (h1 : ¬p) (h2 : ¬q) : ¬(p ∨ q) :=
  fun (h3 : p ∨ q) => 
    have pthenr := fun (h4 : p) => h1 h4
    have qthenr := fun (h5 : q) => h2 h5

    (h3.elim pthenr) qthenr
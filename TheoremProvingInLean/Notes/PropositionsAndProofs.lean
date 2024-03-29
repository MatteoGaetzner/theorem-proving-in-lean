-- Notes for 'Propositions and Proofs'

-- Namespacing the entire file 
-- avoids conflicts with other notes and solutions
namespace propositions_and_proofs_notes

#check And
#check Or
#check Not

variable (p q r : Prop)

#check p ∧ q
#check (p ∧ q) ∨ r
#check (p ∧ q) → (q ∧ p)

axiom and_comm : (p ∧ q) → (q ∧ p)

variable (a b : Prop)
#check and_comm a b

axiom modus_ponens : (p → q) → p → q

-- Working with Propositions as Types

variable {p : Prop}
variable {q : Prop}

theorem t1_1 : p → q → p := fun hp : p => fun _ : q => hp

#print t1_1

-- Better readability

theorem t1_2 : p -> q -> p := 
  fun hp : p => 
  fun _ : q => 
  show p from hp

-- Using theorem t1 to prove theorem t2

theorem t1_3 (hp : p) (_ : q) : p := hp

#print t1_3

section hp_axiom
  axiom hp : p 

  theorem t2_0 : q -> p := t1_3 hp -- actually unnecessary to use t1_3
  theorem t2_1 : q -> p := fun _ : q => hp -- can be shorter 
  theorem t2_2 : q -> p := hp -- since we can just use hp (proof of p) directly

  #print t2_0
  #print t2_1
  #print t2_2
end hp_axiom

axiom unsound : False

theorem ex : 1 = 0 := False.elim unsound

-- Many ways to write theorem 1
theorem t1_4 {p q : Prop} (hp : p) (_ : q) : p := hp
theorem t1_5 : ∀ {p q : Prop}, p → q → p := 
  fun {p q : Prop} (hp : p) (_ : q) => hp
theorem t1_6 : p → q → p := fun (hp : p) (_ : q) => hp

variable (hp : p)
theorem t1_7 : q → p := fun (_ : q) => hp

#print t1_7

-- Generalizing t1 to different input propositions

variable (hp : p)
theorem t1_8 (p q : Prop) (hp : p) (_ : q) : p := hp

variable (p q r s : Prop)

#print t1_8
#check t1_8 p q 

#check t1_8 p q
#check t1_8 r s
#check t1_8 (r → s) (s → r)

variable (h : r → s)
#check t1_8 (r → s) (s → r) h

variable (p q r s : Prop)

-- t2 says: If we have implications p -> q and q -> r, then we have 
-- the implication p -> r
theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r := 
  fun hₚ : p =>  -- Assume p is true
  show r from h₁ (h₂ hₚ)  -- Then by h_2, q is true. By h_1, r follows.

-- Propositional Logic

variable (p q : Prop)
#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

-- Conjunction 
variable (p q : Prop)
example (hp : p) (hq : q) : p ∧ q := 
  And.intro hp hq

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

variable (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)

variable (xs : List Nat)

#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

-- Two equivalent proofs
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, ⟨h.left, h.right⟩⟩
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩

-- Disjunction 

-- 'left' since we proof left side of or
example (hp : p) : p ∨ q := Or.intro_left q hp 
-- 'right since we proof left side of or
example (hq : q) : p ∨ q := Or.intro_right p hq

variable (p q r : Prop) 

example (h : p ∨ q) : q ∨ p := 
  Or.elim h 
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp) 
    (fun hq : q => 
      show q ∨ p from Or.intro_left p hq)

-- More concise by using 
-- Or.inr === Or.intro_right _
-- and Or.inl === Or.intro_left _
example (h : p ∨ q) : q ∨ p := 
  Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq)

-- Negation and Falsity

example (hpq : p -> q) (hnq: ¬q) : ¬p := 
  -- We want to show that ¬p holds if p → q and ¬q hold. 
  -- Since ¬p is defined as p → False, so the proof is a 
  -- function with signature p → False
  -- Because ¬q === q → False,
  -- hnq is a function that takes a proof of q as input and outputs False,
  -- which is why hnq (hpq hp) === hnq q works here
  fun hp : p => show False from hnq (hpq hp)

 -- principle of explosion
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p ) (hnp : ¬p) : q := absurd hp hnp
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

-- Logical Equivalence

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro 
  (fun h : p ∧ q => 
    show q ∧ p from ⟨And.right h, And.left h⟩)
  (fun h : q ∧ p => 
    show p ∧ q from ⟨And.right h, And.left h⟩)

#check and_swap r s

variable (h : p ∧ q)

-- Iff.mp takes as input (a ↔ b : Prop) and (a : Prop) and returns (b : Prop).
-- Here, (and_swap p q) === p ∧ q ↔ q ∧ p.
-- Hence, given proof (_ : p ∧ q ↔ q ∧ p) and (h : p ∧ q), Iff.mp produces q ∧ p
example : q ∧ p := Iff.mp (and_swap p q) h

variable (p q : Prop)
-- Anonymous constructor notation applied to different constructors in a 
-- single line is possible. Here, the outer anonymous constructor is 
-- Iff.intro, the inner one is And.intro.
theorem and_swap_short : p ∧ q ↔ q ∧ p := 
  ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

example (h : p ∧ q) : q ∧ p := 
  have hp := h.left 
  have hq := h.right 
  show q ∧ p from ⟨hq, hp⟩

example (h : p ∧ q) : q ∧ p := 
  have hp : p := h.left
  -- suffices: Gives us additional assumptions on the left hand side, which 
  -- are our new goals. On the right hand side (of 'from') we have must give 
  -- a proof of the original goal using the additional assumptions.
  -- Here:
  -- new goal: (hq : q)
  -- proof using new assumption: ⟨hq, hp⟩
  suffices hq : q from ⟨hq, hp⟩
  show q from h.right

-- Classical Logic 

open Classical

variable (p : Prop)
#check em p

theorem dne {p : Prop} (h : ¬¬p) : p := 
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- theorem emp (p : Prop) : p ∨ ¬p := 
--   impossible???

-- Proof by contradiction

example (h : ¬¬p) : p :=
  byContradiction
    (
      fun h1 : ¬p => 
        have contr := h h1
        -- The following doesn't work, since (h1 : ¬p) needs 
        -- as input (x : p) to produce False. Hence we need to write 
        -- proof of (h : ¬¬p) first, which takes (h1 : ¬p) as input to 
        -- produce False.
        -- have contr := h1 h 
        contr
    )

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q := 
  Or.elim (em p)
    (fun hp : p => 
      Or.inr
        (show ¬q from -- ¬q = q → False
          fun hq : q => 
            h ⟨hp, hq⟩)) -- ¬(p ∧ q) (p ∧ q) = False
    (fun hnp : ¬p => 
      Or.inl hnp)

end propositions_and_proofs_notes

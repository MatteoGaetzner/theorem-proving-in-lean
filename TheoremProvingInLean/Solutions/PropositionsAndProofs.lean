-- Solutions for 'Propositions and Proofs' exercises

-- Namespacing the entire file 
-- avoids conflicts with other notes and solutions
namespace propositions_and_proofs_solutions

variable (p q r : Prop)

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun h : p ∧ q =>
      ⟨h.right, h.left⟩)
    (fun h : q ∧ p =>
      ⟨h.right, h.left⟩)
example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim
        h 
        (fun hp : p =>
          Or.intro_right q hp)
        (fun hq : q =>
          Or.intro_left p hq)
      )
    (fun h : q ∨ p =>
      Or.elim h 
        (fun hq : q =>
          Or.intro_right p hq)
        (fun hp : p =>
          Or.intro_left q hp)
      )

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    -- (p ∧ q) ∧ r → p ∧ (q ∧ r)
    (fun h : (p ∧ q) ∧ r => 
      ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    -- p ∧ (q ∧ r) → (p ∧ q) ∧ r
    (fun h : p ∧ (q ∧ r) => 
      ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    -- (p ∨ q) ∨ r → p ∨ (q ∨ r)
    (fun h : (p ∨ q) ∨ r => 
        Or.elim h 
          (fun hpq : p ∨ q => 
            Or.elim hpq 
              (fun hp : p => 
                Or.inl hp)
              (fun hq : q => 
                Or.inr (Or.inl hq)))
          (fun hr : r => 
            Or.inr (Or.inr hr)))
    -- p ∨ (q ∨ r) → (p ∨ q) ∨ r
    (fun h : p ∨ (q ∨ r) => 
      Or.elim h 
      (fun hp : p => 
        Or.inl (Or.inl hp))
      (fun hqr : q ∨ r =>
        Or.elim hqr 
          (fun hq : q =>
            Or.inl (Or.inr hq))
          (fun hr : r => 
            Or.inr hr)))

-- Distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro 
    -- Proof of: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) 
    (fun hpqr : p ∧ (q ∨ r) =>
      Or.elim hpqr.right 
        (fun hq : q => 
          Or.inl ⟨hpqr.left, hq⟩)
        (fun hr : r => 
          Or.inr ⟨hpqr.left, hr⟩))
    -- Proof of: (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r)
    (fun hpqpr : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hpqpr 
        (fun hpq : p ∧ q => 
          ⟨hpq.left, Or.inl hpq.right⟩)
        (fun hpr : p ∧ r => 
          ⟨hpr.left, Or.inr hpr.right⟩))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro 
    -- Proof of: p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) 
    (fun hpqr : p ∨ (q ∧ r) =>
      Or.elim hpqr 
        (fun hp : p =>
          ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqr : q ∧ r =>
          ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
    -- Proof of: (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
    (fun hqpr : (p ∨ q) ∧ (p ∨ r) =>
      Or.elim hqpr.left 
        (fun hp : p => Or.inl hp)
        (fun hq : q => 
          Or.elim hqpr.right 
            (fun hp : p => Or.inl hp)
            (fun hr : r => Or.inr ⟨hq, hr⟩)))

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro 
    -- Proof of: (p → (q → r)) → (p ∧ q → r) 
    (fun hpqr : p → (q → r) =>
      (fun hpq : p ∧ q => 
        hpqr hpq.left hpq.right
      ))
    -- Proof of: (p ∧ q → r) → (p → (q → r)) 
    (fun hpqr : p ∧ q → r =>
      (fun (hp : p) (hq : q) => 
        hpqr ⟨hp, hq⟩))
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro 
    -- Proof of: ((p ∨ q) → r) → (p → r) ∧ (q → r)
    (fun hpqr : (p ∨ q) → r => 
      And.intro 
        (fun hp : p =>
          hpqr (Or.inl hp))
        (fun hq : q =>
          hpqr (Or.inr hq)))
    -- Proof of: (p → r) ∧ (q → r) → ((p ∨ q) → r)
    (fun hprqr : (p → r) ∧ (q → r) => 
      (fun hpq : p ∨ q => 
        Or.elim hpq 
          (fun hp : p => hprqr.left hp)
          (fun hq : q => hprqr.right hq)))
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro 
    -- Proof of: ¬(p ∨ q) → ¬p ∧ ¬q = (p ∨ q → False) → ((p → False) ∧ (q → False))
    (fun hnpq : p ∨ q → False =>
      And.intro
        (fun hp : p =>
          hnpq (Or.inl hp))
        (fun hq : q =>
          hnpq (Or.inr hq)))
    -- Proof of: ¬p ∧ ¬q → ¬(p ∨ q) 
    (fun hnpnq : ¬p ∧ ¬q => 
      (fun hpq : p ∨ q => 
        Or.elim hpq 
          (fun hp : p => hnpnq.left hp)
          (fun hq : q => hnpnq.right hq)))
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  (fun hnpnq : (p → False) ∨ (q → False) =>
    (fun hpq : p ∧ q => 
      Or.elim hnpnq 
        (fun hnp : p → False => 
          hnp hpq.left) 
        (fun hnq : q → False =>
          hnq hpq.right)))
example : ¬(p ∧ ¬p) := 
  (fun hpnp : p ∧ ¬p => 
    hpnp.right hpnp.left)
example : p ∧ ¬q → ¬(p → q) := 
  (fun hpnq : p ∧ ¬q => 
    (fun hpq : p → q => 
      have hq : q := hpq hpnq.left
      hpnq.right hq))
example : ¬p → (p → q) := 
  (fun hnp : p → False => 
    (fun hp : p => absurd hp hnp))
example : (¬p ∨ q) → (p → q) := 
  (fun hnpq : ¬p ∨ q => 
    (fun hp : p => 
      Or.elim hnpq 
      (fun hnp : ¬p => absurd hp hnp)
      (fun hq : q => hq)))
example : p ∨ False ↔ p := 
  Iff.intro 
    (fun hpf : p ∨ False =>
      Or.elim hpf
        (fun hp : p => hp)
        (fun hf : False => False.elim hf))
    (fun hp : p => Or.inl hp)
example : p ∧ False ↔ False := 
  Iff.intro 
    (fun hpf : p ∧ False => hpf.right)
    (fun hf : False => False.elim hf)
example : (p → q) → (¬q → ¬p) :=
  fun hpq : p → q => 
    fun hnq : q → False => 
      fun hp : p => hnq (hpq hp)

-- Proofs requiring classical logic (Law of Excluded Middle)
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := 
  (fun hpqr : p → q ∨ r => 
    Or.elim (em p)
      (fun hp : p => 
        have hqr : q ∨ r := hpqr hp
        Or.elim hqr 
          (fun hq : q => Or.inl (fun _ : p => hq))
          (fun hr : r => Or.inr (fun _ : p => hr)))
      (fun hnp : ¬p =>
        Or.inl (fun hp : p => absurd hp hnp)))
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  (fun hnpq : p ∧ q → False =>
    (Or.elim (em p)
      (fun hp : p =>
        Or.elim (em q)
          (fun hq : q => False.elim (hnpq ⟨hp, hq⟩))
          (fun nhq : ¬q => Or.inr nhq)))
      (fun hnp : ¬p => Or.inl hnp))
example : ¬(p → q) → p ∧ ¬q := 
  (fun hnpq : (p → q) → False => 
    Or.elim (em p)
    (fun hp : p =>
      Or.elim (em q)
        (fun hq : q =>
          False.elim (hnpq (fun _ : p => hq)))
        (fun nhq : ¬q => 
          ⟨hp, nhq⟩))
    (fun hnp : ¬p =>
      False.elim (hnpq (fun hp : p => absurd hp hnp))))
example : (p → q) → (¬p ∨ q) := 
  fun hpq : p → q => 
    Or.elim (em p)
      (fun hp : p => Or.inr (hpq hp))
      (fun hnp : ¬p => Or.inl hnp)
example : (¬q → ¬p) → (p → q) := 
  fun hnqnp : (¬q → ¬p) => 
    Or.elim (em q)
      (fun hq : q => (fun _ => hq))
      (fun hnq : ¬q => 
        have hnp : ¬p := hnqnp hnq
        fun hp : p => absurd hp hnp)
example : p ∨ ¬p := 
  em p
example : (((p → q) → p) → p) := 
  fun hpqp : (p → q) → p =>
    (Or.elim (em p) 
      (fun hp : p => hp)
      (fun hnp : ¬p => 
          hpqp (fun hp : p => absurd hp hnp)))

-- Harder proof (at least without LEM)
example : ¬(p ↔ ¬p) :=
  fun hpnp : p ↔ ¬p =>
    have hnp : ¬p := fun hp : p => (hpnp.mp hp) hp
    hnp (hpnp.mpr hnp)

end propositions_and_proofs_solutions

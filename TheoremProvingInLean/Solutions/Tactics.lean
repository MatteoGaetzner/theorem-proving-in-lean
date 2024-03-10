-- Solutions for 'Tactics' exercises

-- Namespacing the entire file 
-- avoids conflicts with other notes and solutions

namespace tactics_solutions
  -- Propositions and Proofs

  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := by 
    apply Iff.intro <;> {
      intro h
      apply And.intro h.right h.left
    }

  example : p ∨ q ↔ q ∨ p := by
    apply Iff.intro <;> {
      intro h
      cases h with
      | inl hp => apply Or.inr; exact hp
      | inr hq => apply Or.inl; exact hq
    }


  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
    apply Iff.intro 
    . intro h 
      match h with 
      | ⟨⟨hp, hq⟩, hr⟩ => 
        constructor <;> (try constructor) <;> assumption
    . intro h 
      match h with 
      | ⟨hp, hq, hr⟩ =>
        constructor <;> (try constructor) <;> assumption
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
    apply Iff.intro 
    . intro h 
      cases h with 
      | inl hpq => 
        cases hpq with 
        | inl hp => apply Or.inl; exact hp
        | inr hq => apply Or.inr; apply Or.inl; exact hq
      | inr hr => apply Or.inr; apply Or.inr; exact hr
    . intro h 
      cases h with 
      | inl hp => apply Or.inl; apply Or.inl; assumption
      | inr hqr => 
        cases hqr with 
        | inl hq => apply Or.inl; apply Or.inr; assumption
        | inr hr => apply Or.inr; assumption

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ False ↔ p := sorry
  example : p ∧ False ↔ False := sorry
  example : (p → q) → (¬q → ¬p) := sorry
end tactics_solutions

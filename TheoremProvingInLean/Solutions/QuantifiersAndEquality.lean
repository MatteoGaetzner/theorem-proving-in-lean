-- Solutions for 'Quantifiers and Equality' exercises


-- Namespacing the entire file 
-- avoids conflicts with other notes and solutions
namespace quantifiers_and_equality_solutions

-- Universal Quantifier Theorems

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  Iff.intro 
    (fun h_left => 
      And.intro 
        (fun x => (h_left x).left)
        (fun x => (h_left x).right))
    (fun h_right => 
      fun x => ⟨h_right.left x, h_right.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  fun h1 => fun h2 => fun x => h1 x (h2 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h => fun x => Or.elim h 
    (fun h_left => Or.inl (h_left x)) 
    (fun h_right => Or.inr (h_right x))

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  fun a => Iff.intro 
    (fun hl => hl a)
    (fun hr => fun _ => hr)

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
    Iff.intro 
    (fun h_left => (Or.elim (em r)
      (fun hr : r => Or.inr hr)
      (fun hnr : ¬r => Or.inl 
        (fun x : α => Or.elim (h_left x)
          (fun hpx : p x => hpx)
          (fun hr : r => absurd hr hnr)
        ))))
    (fun h_right => fun x => 
      Or.elim h_right 
        (fun hpx => Or.inl (hpx x))
        (fun hr => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro 
    (fun h_left => fun hr => fun x => 
      (h_left x) hr)
    (fun h_right => fun x => fun r => 
      (h_right r) x)
      
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
  have h_nsbb : ¬ shaves barber barber := 
    fun as_contr : shaves barber barber =>
      ((h barber).mp as_contr) as_contr
  have h_sbb : shaves barber barber := 
    (h barber).mpr h_nsbb
  show False from h_nsbb h_sbb

-- Famous Conjectures

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def even (n : Nat) : Prop := ∃ b, n = 2 * b

def prime (n : Nat) : Prop := n > 1 ∧ ∀ a, (a ≠ n) -> ¬(divides a n)

def infinitely_many_primes : Prop := ∀ n, ∃ a, (a > n) ∧ (prime a)

def Fermat_prime (n : Nat) : Prop := 
  prime n ∧ ∃ k, (k > 0) ∧ (n = 2^k + 1)

def infinitely_many_Fermat_primes : Prop := 
  ∀ a, ∃ n, (n > a) ∧ (Fermat_prime n)

def goldbach_conjecture : Prop := 
  ∀ n, ∃ p1 p2, (prime p1) ∧ (prime p2) ∧ (n = p1 + p2)

def Goldbach's_weak_conjecture : Prop := 
  ∀ n, ((n > 5) ∧ ¬(even n)) 
    → (∃ p1 p2 p3, (prime p1) ∧ 
                   (prime p2) ∧ 
                   (prime p3) ∧ 
                   (n = p1 + p2 + p3))

def Fermat's_last_theorem : Prop := 
  ∀ n : Nat, (n > 2) → (∃ a b c : Nat, a^n + b^n = c^n)

-- Existential Quantifier Theorems

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r := 
  fun h => Exists.elim h fun _x => fun hx => hx
  
example (a : α) : r → (∃ _x : α, r) := 
  fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro 
    (fun ⟨x, hx⟩ => ⟨⟨x, hx.left⟩, hx.right⟩)
    (fun ⟨⟨x, hx⟩, hr⟩ => ⟨x, ⟨hx, hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro 
    (fun ⟨x, hx⟩ => hx.elim 
      (fun hpx => Or.inl ⟨x, hpx⟩) 
      (fun hqx => Or.inr ⟨x, hqx⟩))
    (fun hor => hor.elim 
      (fun ⟨x, hpx⟩ => ⟨x, Or.inl hpx⟩)
      (fun ⟨x, hqx⟩ => ⟨x, Or.inr hqx⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  Iff.intro 
    (fun hp => fun ⟨x, hnpx⟩ => hnpx (hp x))
    (fun h_no_ex => fun x => 
      Or.elim (em (p x))
        (fun hpx => hpx)
        (fun hnpx => absurd ⟨x, hnpx⟩ h_no_ex))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro 
    (fun ⟨x, hpx⟩ => fun hnp => (hnp x) hpx)
    (fun h_n_fa_npx => Or.elim (em (∃ x, p x))
      (fun hp => hp)
      (fun hnp => 
        have h_fa_npx : ∀ x, ¬ p x := 
          (fun x => fun hpx => absurd ⟨x, hpx⟩ hnp)
        absurd h_fa_npx h_n_fa_npx))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
  Iff.intro 
    (fun h_n_ex_px => fun x => fun hpx => absurd ⟨x, hpx⟩ h_n_ex_px )
    (fun h_fa_npx => fun ⟨x, hpx⟩ => absurd hpx (h_fa_npx x))

theorem nfa_iff_exn : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  Iff.intro 
    (fun h_nfa_px : ¬ ∀ x, p x => byContradiction 
      (fun h_nex_np : ¬ ∃ x, ¬ p x =>
        have h_fa_px : ∀ x, p x := 
          (fun hx => byContradiction 
            (fun hpx : ¬p hx => h_nex_np ⟨hx, hpx⟩))
        absurd h_fa_px h_nfa_px))
    (fun ⟨x, hnpx⟩ => 
      fun h_fa_px : ∀ x, p x => 
        absurd (h_fa_px x) hnpx)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro 
    (fun h_x_px_imp_r : ∀ x, p x → r => 
      fun ⟨x, hpx⟩ => (h_x_px_imp_r x) hpx)
    (fun h_ex_x_px_imp_r : (∃ x, p x) → r => 
      fun x => fun hpx => h_ex_x_px_imp_r ⟨x, hpx⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro 
    (fun ⟨x_ex, h_px_imp_r⟩ => fun h_fa_px => 
      have hp_x_ex := h_fa_px x_ex
      h_px_imp_r hp_x_ex
    )
    (fun h_fa_imp_r => Or.elim (em (∀ x, p x)) 
      (fun h_fa_px => 
        have hr := h_fa_imp_r h_fa_px
        ⟨a, fun _x => hr⟩
      )
      (fun h_nfa_px => 
        have hnp : ∃ x, ¬p x := (nfa_iff_exn α p).mp h_nfa_px 
        let ⟨x, hnpx⟩ := hnp
        ⟨x, fun hpx => absurd hpx hnpx⟩
      )
    )

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  Iff.intro 
    (fun ⟨x, h_r_imp_px⟩ => fun r => ⟨x, h_r_imp_px r⟩)
    (fun h_r_imp_ex => Or.elim (em r) 
      (fun hr => 
        let ⟨x, hpx⟩ := h_r_imp_ex hr
        ⟨x, fun _ => hpx⟩
      )
      (fun hnr => ⟨a, fun hr => absurd hr hnr⟩)
    )

end quantifiers_and_equality_solutions

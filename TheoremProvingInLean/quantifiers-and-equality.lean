-- Quantifiers and Equality

-- The Universal Quantifier

-- Show a for-all proposition given another for-all prpoposition

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)

-- explicit version

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

-- implicit version (note the curly braces {x y z})

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd


-- Equality

#check Eq.refl    -- ∀ (a : ?m.1), a = a
#check Eq.symm    -- ?m.2 = ?m.3 → ?m.3 = ?m.2
#check Eq.trans   -- ?m.2 = ?m.3 → ?m.3 = ?m.4 → ?m.2 = ?m.4

universe u

#check @Eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d := (hab.trans hcb.symm).trans hcd

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

-- Calculational Proofs

-- calc
--   <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
--   '_'       'op_2'  <expr>_2  ':='  <proof>_2
--   ...
--   '_'       'op_n'  <expr>_n  ':='  <proof>_n

-- calc <expr>_0 
--     '_' 'op_1' <expr>_1 ':=' <proof>_1
--     '_' 'op_2' <expr>_2 ':=' <proof>_2
--     ...
--     '_' 'op_n' <expr>_n ':=' <proof>_n

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T_1 : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

theorem T_2 : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

theorem T_3 : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

theorem T_4 : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " ∣ " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x ∣ y   := h₁
    _ = z   := h₂
    _ ∣ 2*z := divides_mul ..

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

-- The Existential Quantifier

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

theorem even_plus_even_1 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

-- Exercises

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

-- Notes for 'Dependent Type Theory'

-- Namespacing the entire file 
-- avoids conflicts with other notes and solutions
namespace dependent_type_theory_notes


/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

-- Types as objects
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type

#check List α    -- Type
#check List Nat  -- Type

#check Type      -- Type 1

#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

#check Type
#check Type 0

#check List    -- Type u_1 → Type u_1

#check Prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)

universe u

def Fp (α : Type u) : Type u := Prod α α

#check Fp    -- Type u → Type u

-- Function Abstraction and Evaluation

#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x : Nat => x + 5     -- Nat inferred
#check λ x : Nat => x + 5       -- Nat inferred

#eval (λ x : Nat => x + 5) 10    -- 15

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

def f_dtt (n : Nat) : String := toString n
def g_dtt (s : String) : Bool := s.length > 1

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g_dtt (f_dtt x)  -- Nat → Bool
#check fun x => g_dtt (f_dtt x)        -- Nat → Bool

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

-- def f (n : Nat) : String := toString n
-- def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g_dtt f_dtt 0
  -- Bool

#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

-- def f (n : Nat) : String := toString n
-- def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g_dtt f_dtt 0
  -- Bool

#eval g_dtt (f_dtt 1)

-- Definitions

def double (x : Nat) : Nat :=
  x + x

#eval double 3    -- 6

-- def double : Nat → Nat :=
--   fun x => x + x
--
-- #eval double 3    -- 6

-- def double :=
--   fun (x : Nat) => x + x

def pi := 3.141592654

def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5

-- def add (x : Nat) (y : Nat) :=
--   x + y

#eval add (double 3) (7 + 9)  -- 22

def greater (x y : Nat) :=
  if x > y then x
  else y

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8

def compose_0 (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
 g (f x)
def double_0 (x : Nat) : Nat :=
 x + x
def square (x : Nat) : Nat :=
  x * x

#eval compose_0 Nat Nat Nat double_0 square 3  -- 18


-- Local Definitions 

#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16

#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/

-- Variables and Sections

-- Least compact

def compose_1 (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice_1 (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice_1 (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

-- More compact

variable (α β γ : Type)

def compose_2 (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice_2 (h : α → α) (x : α) : α :=
  h (h x)

def doThrice_2 (h : α → α) (x : α) : α :=
  h (h (h x))

-- Most compact 

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose_3 := g (f x)
def doTwice_3 := h (h x)
def doThrice_3 := h (h (h x))

#print compose_3
#print doTwice_3
#print doThrice_3

-- Sections: Limiting variable scope

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose_4 := g (f x)
  def doTwice_4 := h (h x)
  def doThrice_4 := h (h (h x))
end useful


namespace Foo
  def ap : Nat := 5
  def fp (x : Nat) : Nat := x + 7

  def fa : Nat := fp ap
  def ffa : Nat := fp (fp ap)

  #check ap
  #check fp
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check ap  -- error
-- #check fp  -- error
#check Foo.ap
#check Foo.fp
#check Foo.fa
#check Foo.ffa

open Foo

#check ap
#check fp
#check fa
#check Foo.fa

#check List.nil
#check List.cons
#check List.map

-- open List
--
-- #check nil
-- #check cons
-- #check map

namespace Foo
  def app : Nat := 5
  def fpp (x : Nat) : Nat := x + 7

  def fap : Nat := fpp app

  namespace Bar
    def ffa : Nat := fpp (fpp app)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fap
#check Foo.Bar.ffa

open Foo

#check fap
#check Bar.ffa

namespace Foo2
  def a : Nat := 5
  def fp (x : Nat) : Nat := x + 7

  def fa : Nat := fp a
end Foo2

#check Foo2.a
#check Foo2.fp

namespace Foo2
  def ffa : Nat := fp (fp a)
end Foo2

-- What makes dependent type theory dependent?

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α

#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α

universe u1 v

-- Functions f1, g1 pairs of (x, f(x)) for arbitrary types of x and images of f

def f1 (α : Type u1) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g1 (α : Type u1) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f1 Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g1 Type (fun α => α) Nat x).2

#eval h2 5 -- 5

-- Implicit Arguments

universe u2

def Lst (α : Type u2) : Type u2 := List α

def Lst.cons {α : Type u2} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u2} : Lst α := List.nil
def Lst.append {α : Type u2} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs

universe u3
def ident {α : Type u3} (x : α) := x

#check ident
#check ident 1       
#check ident "hello" 
#check @ident        

universe u4

section
  variable {α : Type u}
  variable (x : α)
  def ident1 := x
end

#check ident1
#check ident1 4
#check ident1 "hello"

#check List.nil
#check id

#check (List.nil : List Nat)
#check (id : Nat → Nat)

#check 2
#check (2 : Nat)
#check (2 : Int)

#check @id
#check @id Nat
#check @id Bool

#check @id Nat 1
#check @id Bool true

end dependent_type_theory_notes

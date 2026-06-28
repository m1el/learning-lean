/- §2.1. Simple Type Theory -/
/- Here are some examples of how you can declare objects in Lean and check their types. -/
/- Define some constants. -/
namespace sect2_1
def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
-- "&&" is the Boolean and
#check b1 && b2
-- Boolean or
#check b1 || b2
-- Boolean "true"
#check true
/- Evaluate -/

#eval 5 * 4
#eval m + 2
#eval b1 && b2


#check Nat → Nat
#check Nat -> Nat
#check Nat × Nat
#check Prod Nat Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat × Nat → Nat
#check (Nat → Nat) → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add
#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2
#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1
#eval (5, 9).2
end sect2_1
/- §2.2. Types as objects -/
namespace sect2_2
/- entities like Nat and Bool—are first-class citizens,
which is to say that they themselves are objects -/
#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

/- You can also declare new constants for types: -/
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

/- As the example above suggests, you have already seen an example of a function of type Type → Type → Type, namely, the Cartesian product Prod: -/
--def α : Type := Nat
--def β : Type := Bool

#check Prod α β
#check α × β
#check Prod Nat Nat
#check Nat × Nat

-- def α : Type := Nat

#check List α
#check List Nat
#check Type


/-hierarchy of types-/
#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Type
#check Type 0
/-Some operations, however, need to be polymorphic over type universes-/
#check List
#check Prod

/-To define polymorphic constants, Lean allows you to declare universe variables explicitly using the universe command:-/
universe u

def F1 (α : Type u) : Type u := Prod α α

#check F1

def F2.{v} (α : Type v) : Type v := Prod α α

#check F2
end sect2_2

/- §2.3. Function Abstraction and Evaluation -/
namespace sect2_3
#check fun (x : Nat) => x + 5
-- λ and fun mean the same thing
#check λ (x : Nat) => x + 5

#check fun x => x + 5
#check λ x => x + 5
#eval (λ x : Nat => x + 5) 10
#eval (λ x => x + 5) 10


#check fun x : Nat => fun y : Bool =>
  if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) =>
  if not y then x + 1 else x + 2
#check fun x y =>
  if not y then x + 1 else x + 2


def f (n : Nat) : String := ToString.toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x
#check fun _x : Nat => true
#check fun x : Nat => g (f x)
#check fun x => g (f x)

/-higher-order functions-/
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)


#check (fun x : Nat => x) 1
#check (fun _x : Nat => true) 1
def f2 (n : Nat) : String := toString n
def g2 (s : String) : Bool := s.length > 0

#check (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) =>
  u (v x)) Nat String Bool g2 f2 0


#eval (fun x : Nat => x) 1
#eval (fun _x : Nat => true) 1
end sect2_3

/- §2.4. Definitions -/
namespace sect2_4
def double (x : Nat) : Nat :=
  x + x
#eval double 3

def double2 : Nat→Nat := λx => x+x
#eval double2 3


def pi := 3.141592654
def add (x y : Nat) :=
  x + y

#eval add 3 2

def add2 (x : Nat) (y : Nat) :=
  x + y

#eval add2 (double 3) (7 + 9)

def greater (x y : Nat) :=
  if x > y then x
  else y

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2


def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3
end sect2_4

/- §2.5. Local Definitions -/
namespace sect2_5

#check let y := 2 + 2; y * y
#eval  let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2

#check let y := 2 + 2;
  let z := y + y;
  z * z
#eval  let y := 2 + 2;
  let z := y + y;
  z * z
end sect2_5
/- §2.6. Variables and Sections -/
namespace sect2_6_1
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

end sect2_6_1

namespace sect2_6_2
  variable (α β γ : Type)
  def compose (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

  def doTwice (h : α → α) (x : α) : α :=
    h (h x)

  def doThrice (h : α → α) (x : α) : α :=
    h (h (h x))
end sect2_6_2

namespace sect2_6_3
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))

  #print compose
  #print doTwice
  #print doThrice
end sect2_6_3

/- §2.7. Namespaces -/
namespace sect2_7
  namespace Foo
    def a : Nat := 5
    def f (x : Nat) : Nat := x + 7

    def fa : Nat := f a
    def ffa : Nat := f (f a)

    #check a
    #check f
    #check fa
    #check ffa
    #check Foo.ffa
  end Foo

  -- #check a  -- error
  -- #check f  -- error
  #check Foo.a
  #check Foo.f
  #check Foo.fa
  #check Foo.ffa
  open Foo

  #check a
  #check f
  #check fa
  #check Foo.fa
end sect2_7
/- §2.8. What makes dependent type theory dependent? -/
namespace sect2_8
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat
#check cons Bool
#check cons

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5
def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5
end sect2_8


/- §2.9. Implicit Arguments -/
namespace sect2_9_1
  universe u
  def Lst (α : Type u) : Type u := List α
  def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil (α : Type u) : Lst α := List.nil
  def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
  #check Lst
  #check Lst.cons
  #check Lst.nil
  #check Lst.append

  #check Lst.cons Nat 0 (Lst.nil Nat)
  def as : Lst Nat := Lst.nil Nat
  def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

  #check Lst.append Nat as bs

  #check Lst
  #check Lst.cons
  #check Lst.nil
  #check Lst.append
end sect2_9_1
namespace sect2_9_2
  universe u
  def Lst (α : Type u) : Type u := List α
  def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil (α : Type u) : Lst α := List.nil
  def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
  #check Lst
  #check Lst.cons
  #check Lst.nil
  #check Lst.append
  #check Lst.cons _ 0 (Lst.nil _)def as : Lst Nat := Lst.nil _
  def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

  #check Lst.append _ as bs
end sect2_9_2
namespace sect2_9_3
  universe u
  def Lst (α : Type u) : Type u := List α

  def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil {α : Type u} : Lst α := List.nil
  def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

  #check Lst.cons 0 Lst.nil
  def as : Lst Nat := Lst.nil
  def bs : Lst Nat := Lst.cons 5 Lst.nil

  #check Lst.append as bs

  def ident {α : Type u} (x : α) := x

  #check (ident)
  #check ident 1
  #check ident "hello"
  #check @ident
end sect2_9_3
namespace sect2_9_4
  universe u

  section
    variable {α : Type u}
    variable (x : α)
    def ident := x
  end

  #check ident
  #check ident 4
  #check ident "hello"

  #check (List.nil)
  #check (id)
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
end sect2_9_4

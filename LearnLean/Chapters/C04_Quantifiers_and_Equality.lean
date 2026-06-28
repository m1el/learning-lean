/- §4.1. The Universal Quantifier -/
namespace sect4_1
example (α : Type) (p q : α → Prop) :
    (∀ (x : α), p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ (x : α), p x ∧ q x =>
  fun y : α =>
    (h y).left
  --show p y from (h y).left

example (α : Type) (p q : α → Prop) :
    (∀ (x : α), p x ∧ q x) → ∀ (x : α), p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
    (h z).left
  -- show p z from And.left (h z)


variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ (x y z), r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc
end sect4_1
namespace sect4_1_2
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
  let hbc := (symm_r hcb)
  (trans_r (trans_r hab hbc) hcd)

end sect4_1_2
/- §4.2. Equality -/
namespace sect4_2
#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

example : a = d := (hab.trans hcb.symm).trans hcd

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  h1.subst h2

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

example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

end sect4_2


/- §4.3. Calculational Proofs -/
namespace sect4_3
variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4


variable (a b c d e : Nat)
variable (a b c d e : Nat)

theorem T2
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

variable (a b c d e : Nat)
variable (a b c d e : Nat)
theorem T3
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]


variable (a b c d e : Nat)
variable (a b c d e : Nat)

theorem T4
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]


variable (a b c d e : Nat)
variable (a b c d e : Nat)

theorem T5
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
variable (a b c d : Nat)

/- inequality -/
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

/- custom transitivity -/
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

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..

variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              :=
      by rw [←Nat.add_assoc]

variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   :=
      by rw [←Nat.add_assoc]

variable (x y : Nat)
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

end sect4_3

/- §4.4. The Existential Quantifier -/
namespace sect4_4
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
  Exists.intro 1 h
  -- ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h
  -- ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)
  -- ⟨y, hxy, hyz⟩
  -- ⟨y, ⟨hxy, hyz⟩⟩

end sect4_4


namespace sect4_4_1
variable (g : Nat → Nat → Nat)

theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments

#print gex1
#print gex2
#print gex3
#print gex4
set_option pp.explicit false  -- undo
end sect4_4_1

namespace sect4_4
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
  -- | Exists.intro w hw => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def IsEven (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

theorem even_plus_even2 (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

end sect4_4

/- §4.5. More on the Proof Language -/
namespace sect4_5
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have h1: f 0 ≤ f 1 := h 0
  have h2: f 0 ≤ f 2 := Nat.le_trans h1 (h 1)
  show f 0 ≤ f 3 from Nat.le_trans h2 (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

-- notation "‹" p "›" => show p by assumption

-- variable (f : Nat → Nat)
-- variable (h : ∀ x : Nat, f x ≤ f (x + 1))

-- example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
--   fun _ : f 0 ≥ f 1 =>
--   fun _ : f 1 ≥ f 2 =>
--   have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
--   have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
--   show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

end sect4_5
/- §4.6. Exercises -/
namespace sect4_6
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun hxpx_qx =>
      And.intro
        (fun x => (hxpx_qx x).left)
        (fun x => (hxpx_qx x).right))
    (fun hxpx_qx =>
      (fun x => And.intro
        (hxpx_qx.left x)
        (hxpx_qx.right x)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (fun hpx_qx hpx x => (hpx_qx x) (hpx x))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun hpx_qx x => Or.elim hpx_qx
    (fun hpx => Or.inl (hpx x))
    (fun hqx => Or.inr (hqx x)))


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ (x : men), shaves barber x ↔ ¬ shaves x x) : False :=
  let co := shaves barber barber
  (h barber).elim
    (fun fwd: co → ¬co => fun bwd: ¬co → co =>
      let not_shaves : ¬co := fun s => (fwd s) s
      not_shaves (bwd not_shaves))

def even (n : Nat) : Prop := ∃ m, n = 2 * m

def compound (n: Nat) : Prop :=
  ∃ a b, (a > 1 ∧ a < n ∧ b > 1 ∧ b < n) ∧ n = a * b
def prime (n : Nat) : Prop := n > 1 ∧ ¬ (compound n)

def infinitely_many_primes : Prop :=
  ∀ (n: Nat), ∃ m, m > n ∧ prime m

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ k, n = 2^2^k + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ (n: Nat), ∃ m, m > n ∧ Fermat_prime m

def goldbach_conjecture : Prop :=
  ∀ (n: Nat), ∃ (a b: Nat),
    prime a ∧ prime b ∧
    2 * n + 4 = a + b

def Goldbach's_weak_conjecture : Prop :=
  ∀ (n: Nat), ∃ (a b c: Nat),
    prime a ∧ prime b ∧ prime c ∧
    2 * n + 7 + 1 = a + b + c

def Fermat's_last_theorem : Prop :=
  ¬ ∃ (n a b c: Nat), (a+1)^(n+2) + (b+1)^(n+2) = (c+1)^(n+2)

end sect4_6

namespace sect4_6_1

-- theorem not_forall {α: Type} (p: α → Prop):
--   (∀ x, p x) ↔ ¬(∃ x, ¬p x) :=
--     Iff.intro
--       (fun haxpx => fun hexnpx =>
--         Exists.elim hexnpx
--           (fun x npx => npx (haxpx x)))
--       (fun hnexnpx => fun hexnpx => sorry)
theorem not_exists {α: Type} (p: α → Prop):
  (∀ x: α, ¬p x) ↔ ¬(∃ x: α, p x) :=
    Iff.intro
      (fun haxnpx ⟨x, hpx⟩ => (haxnpx x) hpx)
      (fun hnexpx x hpx => hnexpx ⟨x, hpx⟩)

-- example {p q : Prop} : (¬p ↔ q) ↔ (p ↔ ¬q) := by simp
end sect4_6_1

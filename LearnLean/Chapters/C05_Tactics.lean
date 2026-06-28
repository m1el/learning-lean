/- §5.1. Entering Tactic Mode -/
namespace sect5_1

-- theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
--   sorry

theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

theorem test4 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

theorem test5 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp
end sect5_1

/- §5.2. Basic Tactics -/
namespace sect5_2
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example : ∀ a b c : Nat, a = b → a = c → c = b :=
  fun _a _b _c hab hac =>
    Eq.trans (Eq.symm hac) hab

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃

variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

example (y : Nat) : (fun _x : Nat => 0) y = 0 := by
  rfl

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption

example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

-- example : 2 + 3 = 5 := by
--   generalize 3 = x
--   sorry

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

end sect5_2

/- §5.3. More Tactics -/
namespace sect5_3
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor; exact hp; apply Or.inr; exact hr

def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_pair2 : α × β → β × α :=
  (fun ab => Prod.mk ab.snd ab.fst)

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

def swap_sum2 : Sum α β → Sum β α :=
  (fun ab: Sum α β => ab.elim Sum.inr Sum.inl)
  -- (fun ab: Sum α β => Sum.elim Sum.inr Sum.inl ab)
  -- Sum.elim Sum.inr Sum.inl
  -- .elim .inr .inl

open Nat
example (P : Nat → Prop)
    (h₀ : P 0) (h₁ : ∀ n, P (succ n))
    (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption
end sect5_3

/- §5.4. Structuring Tactic Proofs -/
namespace sect5_4
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this

example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
end sect5_4
/- §5.5. Tactic Combinators -/
namespace sect5_5

example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

end sect5_5
/- §5.6. Rewriting -/
namespace sect5_6
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption

variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

variable (a b : Nat) (f : Nat → Nat)

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

end sect5_6
/- §5.7. Using the Simplifier -/
namespace sect5_7
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]

example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

namespace local1
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
end local1

namespace local2
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat) (_p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption
end local2

def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]

variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]

variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_comm]

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

namespace local3
set_option linter.unusedVariables false
set_option linter.unusedVariables false
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

set_option linter.unusedVariables true
set_option linter.unusedVariables true
end local3

def mk_symm (xs : List α) :=
  xs ++ xs.reverse

theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
namespace local4
@[local simp] theorem reverse_mk_symm2 (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end local4

namespace local5
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end local5
end sect5_7

/- §5.8. Split Tactic-/
namespace sect5_8
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

example (x y z : Nat) :
  x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w →
  f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl

def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, _] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp +arith at h

end sect5_8
/- §5.9. Extensible Tactics -/
namespace sect5_9
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
end sect5_9

/- §5.10. Exercises-/
namespace sect5_10_C03
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun ⟨hp, hq⟩ => ⟨hq, hp⟩)
    (fun ⟨hq, hp⟩ => ⟨hp, hq⟩)

-- example : p ∧ q ↔ q ∧ p := by rw [And.comm]
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun pq: p∨q => match pq with
      | .inl p => .inr p
      | .inr q => .inl q)
    (fun qp: q∨p => match qp with
      | .inl q => .inr q
      | .inr p => .inl p)

example : p ∨ q ↔ q ∨ p :=
  let or_swap {a b: Prop} : (Or a b) → (Or b a) :=
    fun
      | .inl ha => .inr ha
      | .inr hb => .inl hb
  Iff.intro or_swap or_swap

-- example : p ∨ q ↔ q ∨ p := by rw [Or.comm]
example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  · intro pq
    cases pq with
    | inl hp => exact (Or.inr hp)
    | inr hq => exact (Or.inl hq)
  · intro pq
    cases pq with
    | inl hp => exact (Or.inr hp)
    | inr hq => exact (Or.inl hq)

example : p ∨ q ↔ q ∨ p := by
  have or_swap {a b: Prop} : (Or a b) → (Or b a) := by
    rintro (ha | hb)
    · exact .inr ha
    · exact .inl hb
  apply Iff.intro
  · exact or_swap
  · exact or_swap

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, ⟨hq, hr⟩⟩)
    (fun ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, ⟨hq, hr⟩⟩
  · intro ⟨hp, ⟨hq, hr⟩⟩
    exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun
      | .inl (.inl p) => .inl p
      | .inl (.inr q) => .inr (.inl q)
      | .inr r        => .inr (.inr r))
    (fun
      | .inl p        => .inl (.inl p)
      | .inr (.inl q) => .inl (.inr q)
      | .inr (.inr r) => .inr r)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  · intro pq_r
    cases pq_r with
    | inl pq =>
      cases pq with
      | inl hp => exact .inl hp
      | inr hq => exact .inr (.inl hq)
    | inr hr   => exact .inr (.inr hr)
  · intro p_qr
    cases p_qr with
    | inl p => exact .inl (.inl p)
    | inr qr =>
      cases qr with
      | inl q => exact .inl (.inr q)
      | inr r => exact .inr r

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  · rintro ((hp | hq) | hr)
    · exact .inl hp
    · exact .inr (.inl hq)
    · exact .inr (.inr hr)
  · rintro (hp | (hq | hr))
    · exact .inl (.inl hp)
    · exact .inl (.inr hq)
    · exact .inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun
      | ⟨hp, .inl hq⟩ => .inl ⟨hp, hq⟩
      | ⟨hp, .inr hr⟩ => .inr ⟨hp, hr⟩)
    (fun
      | .inl ⟨hp, hq⟩ => ⟨hp, .inl hq⟩
      | .inr ⟨hp, hr⟩ => ⟨hp, .inr hr⟩)

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact .inl ⟨hp, hq⟩
    | inr hr => exact .inr ⟨hp, hr⟩
  · intro hpq_pr
    cases hpq_pr with
    | inl hpq => exact ⟨hpq.left, (.inl hpq.right)⟩
    | inr hpr => exact ⟨hpr.left, (.inr hpr.right)⟩


example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · rintro ⟨hp, (hq | hr)⟩
    · exact .inl ⟨hp, hq⟩
    · exact .inr ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, .inl hq⟩
    · exact ⟨hp, .inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun
      | .inl hp       => ⟨.inl hp, .inl hp⟩
      | .inr ⟨hq, hr⟩ => ⟨.inr hq, .inr hr⟩)
    (fun
      | ⟨.inl hp, _hpr⟩     => .inl hp
      | ⟨.inr _hq, .inl hp⟩ => .inl hp
      | ⟨.inr hq, .inr hr⟩  => .inr ⟨hq, hr⟩)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro hp_qr
    cases hp_qr with
    | inl hp  => exact ⟨.inl hp, .inl hp⟩
    | inr hqr => exact ⟨.inr hqr.left, .inr hqr.right⟩
  · intro ⟨hpq, hqr⟩
    cases hpq with
    | inl hp => exact .inl hp
    | inr hq =>
      cases hqr with
      | inl hp => exact .inl hp
      | inr hr => exact .inr ⟨hq, hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · rintro (hp | ⟨hq, hr⟩)
    · exact ⟨.inl hp, .inl hp⟩
    · exact ⟨.inr hq, .inr hr⟩
  · rintro ⟨(hp1 | hq), (hp2 | hr)⟩
    · exact .inl hp1
    · exact .inl hp1
    · exact .inl hp2
    · exact .inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hp_qr ⟨hp, hq⟩ => (hp_qr hp) hq)
    (fun hpq_r hp hq => hpq_r ⟨hp, hq⟩)

example : (p → (q → r)) ↔ (p ∧ q → r) := by simp
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  · intro hp_qr ⟨hp, hq⟩
    exact (hp_qr hp) hq
  · intro hpq_r hp hq
    exact hpq_r ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpq_r: ((p ∨ q) → r) => And.intro
      (fun hp: p => hpq_r (.inl hp))
      (fun hq: q => hpq_r (.inr hq)))
    (fun ⟨hpr, hqr⟩ => fun
      | .inl hp => hpr hp
      | .inr hq => hqr hq)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
 apply Iff.intro
 · intro hpq_r
   apply And.intro
   · intro hp
     exact hpq_r (.inl hp)
   · intro hq
     exact hpq_r (.inr hq)
 · intro ⟨hpr, hqr⟩
   intro hpq
   cases hpq with
   | inl hp => exact hpr hp
   | inr hq => exact hqr hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h1 => ⟨fun hp => h1 (.inl hp), fun hq => h1 (.inr hq)⟩)
    (fun ⟨hnp, hnq⟩ hpq => Or.elim hpq hnp hnq)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by simp
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  · intro h1
    apply And.intro
    · intro hp
      exact h1 (.inl hp)
    · intro hq
      exact h1 (.inr hq)
  · intro ⟨hnp, hnq⟩ hpq
    exact Or.elim hpq hnp hnq

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun hnp_nq ⟨hp, hq⟩ => match hnp_nq with
    | .inl hnp => hnp hp
    | .inr hnq => hnq hq)

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro hnp_nq ⟨hp, hq⟩
  cases hnp_nq with
  | inl hnp => exact hnp hp
  | inr hnq => exact hnq hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  rintro (hnp | hnq) ⟨hp, hq⟩
  · exact hnp hp
  · exact hnq hq

example : ¬(p ∧ ¬p) := (fun ⟨hp, hnp⟩ => hnp hp)
example : ¬(p ∧ ¬p) := by
  intro ⟨hp, hnp⟩
  exact hnp hp

example : p ∧ ¬q → ¬(p → q) :=
  (fun ⟨hp, hnq⟩ hnpq => hnq (hnpq hp))

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ hnpq
  exact hnq (hnpq hp)

example : ¬p → (p → q) :=
  (fun hnp hp => False.elim (hnp hp))

example : ¬p → (p → q) := by
  intro hnp hp
  apply False.elim
  exact hnp hp

example : (¬p ∨ q) → (p → q) :=
  (fun
    | (Or.inl hnp) => fun hp => False.elim (hnp hp)
    | (Or.inr hq) => fun _hp => hq)

example : (¬p ∨ q) → (p → q) := by
  intro hnp_q
  cases hnp_q with
  | inl hnp =>
    intro hp
    exact False.elim (hnp hp)
  | inr hq =>
    intro _hp
    exact hq

example : (¬p ∨ q) → (p → q) := by
  rintro (hnp | hq) hp
  · exact False.elim (hnp hp)
  · exact hq

example : p ∨ False ↔ p :=
  Iff.intro
    (fun
      | .inl hp => hp
      | .inr fa => False.elim fa)
    (fun hp => Or.inl hp)

example : p ∨ False ↔ p := by
  apply Iff.intro
  · intro hp_f
    cases hp_f with
    | inl hp => exact hp
    | inr fa => exact False.elim fa
  · exact Or.inl

example : p ∨ False ↔ p := by
  apply Iff.intro
  · rintro (hp | fa)
    · exact hp
    · exact False.elim fa
  · exact Or.inl

example : p ∧ False ↔ False :=
  Iff.intro And.right False.elim

example : p ∧ False ↔ False := by
  apply Iff.intro
  · exact And.right
  · exact False.elim

example : (p → q) → (¬q → ¬p) :=
  (fun hp_hq hnq hp => hnq (hp_hq hp))

example : (p → q) → (¬q → ¬p) := by
  intro hp_hq hnq hp
  apply hnq
  exact hp_hq hp

end sect5_10_C03

namespace sect5_10_C04
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun hx_hpx_hqx =>
      ⟨fun x => (hx_hpx_hqx x).left, fun x => (hx_hpx_hqx x).right⟩)
    (fun ⟨hxpx, hxqx⟩ x => ⟨hxpx x, hxqx x⟩)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  · intro hx_hpx_hqx
    apply And.intro
    · intro x
      apply (hx_hpx_hqx x).left
    · intro x
      apply (hx_hpx_hqx x).right
  · intro ⟨hxpx, hxqx⟩ x
    apply And.intro
    · exact hxpx x
    · exact hxqx x

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (fun hx_px_qx hx_px hx => (hx_px_qx hx) (hx_px hx))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hx_px_qx hx_px hx
  apply hx_px_qx hx
  apply hx_px hx

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun
    | .inl hx_px => fun hx => Or.inl (hx_px hx)
    | .inr hx_qx => fun hx => Or.inr (hx_qx hx))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h1_2
  cases h1_2 with
  | inl hx_px =>
    intro hx
    apply Or.inl
    exact hx_px hx
  | inr hx_qx =>
    intro hx
    apply Or.inr
    exact hx_qx hx

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  rintro (hx_px | hx_qx) x
  · exact Or.inl (hx_px x)
  · exact Or.inr (hx_qx x)

end sect5_10_C04

namespace sect5_10
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  exact ⟨.inl hp, .inr (.inl hp), .inr (.inr hp)⟩

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  simp [hp]
end sect5_10

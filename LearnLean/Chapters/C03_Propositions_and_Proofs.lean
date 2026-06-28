/- §3.1. Propositions as Types -/
namespace sect3_1
def Implies (p q : Prop) : Prop := p → q
#check And
#check Or
#check Not
#check Implies
variable (p q r : Prop)

#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)

structure Proof (p : Prop) : Type where
  proof : p
#check Proof
axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q

axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

end sect3_1

/- §3.2. Working with Propositions as Types -/
namespace sect3_2
-- set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → (q → p) :=
  fun hp : p =>
    fun _hq : q => hp

#print t1

theorem t1_2 : p → q → p :=
  fun hp : p =>
  fun _hq : q =>
  show p from hp

theorem t1_3 (hp : p) (_hq : q) : p := hp

#print t1_3

axiom hp : p

theorem t2 : q → p := t1 hp


axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound

-- set_option linter.unusedVariables false
-- set_option linter.unusedVariables false
theorem t1_4 {p q : Prop} (hp : p) (_hq : q) : p := hp

#print t1_4


theorem t1_5 : p → q → p := fun (hp : p) (_hq : q) => hp


-- set_option linter.unusedVariables false
-- set_option linter.unusedVariables false
theorem t1_6 (p q : Prop) (hp : p) (_hq : q) : p := hp

variable (p q r s : Prop)

#check t1_6 p q
#check t1_6 r s
#check t1_6 (r → s) (s → r)
variable (h : r → s)
#check t1_6 (r → s) (s → r) h


variable (p q r s : Prop)

theorem t2_2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

end sect3_2

/- §3.3. Propositional Logic -/
namespace sect3_3
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

end sect3_3


/- §3.3.1. Conjunction -/
namespace sect3_3_1
  variable (p q : Prop)

  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

  #check fun (hp : p) (hq : q) => And.intro hp hq

  example (h : p ∧ q) : p := And.left h
  example (h : p ∧ q) : q := And.right h

  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)

  variable (hp : p) (hq : q)

  #check (⟨hp, hq⟩ : p ∧ q)


  variable (xs : List Nat)

  #check List.length xs
  #check xs.length

  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩

  example (h : p ∧ q) : q ∧ p :=
    And.intro h.right h.left
  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩
  example (h : p ∧ q) : p := h.left
  example (h : p ∧ q) : q := h.right
  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, ⟨h.left, h.right⟩⟩

  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, h.left, h.right⟩

end sect3_3_1
/- §3.3.2. Disjunction -/
namespace sect3_3_2
  variable (p q : Prop)
  example (hp : p) : p ∨ q := Or.intro_left q hp
  example (hq : q) : p ∨ q := Or.intro_right p hq

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
  example (h : p ∨ q) : q ∨ p :=
    h.elim (λhp => Or.inr hp) (λhq => Or.inl hq)
end sect3_3_2

/- §3.3.3. Negation and Falsity -/
namespace sect3_3_3
  variable (p q : Prop)
  -- (p → q) → ¬q → ¬p
  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)
  example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
  example (hp : p) (hnp : ¬p) : q := absurd hp hnp
  example {r} (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp

end sect3_3_3
/- §3.3.4. Logical Equivalence -/
namespace sect3_3_4
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))
#check and_swap p q

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

theorem and_swap2 : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩
example (h : p ∧ q) : q ∧ p := (and_swap2 p q).mp h
end sect3_3_4


/- §3.4. Introducing Auxiliary Subgoals -/
namespace sect3_4
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

end sect3_4
/- §3.5. Classical Logic -/
namespace sect3_5
open Classical

variable (p : Prop)

#check em p

open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)

end sect3_5
/- §3.6. Examples of Propositional Validities -/
namespace sect3_6
open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
end sect3_6

/- §3.7. Exercises -/
namespace sect3_7
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λh=>And.intro h.right h.left)
    (λh=>And.intro h.right h.left)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h=>Or.elim h Or.inr Or.inl)
    (fun h=>Or.elim h Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun pq_r: (p ∧ q) ∧ r => And.intro
      pq_r.left.left (And.intro pq_r.left.right pq_r.right))
    (fun p_qr: p ∧ (q ∧ r) => And.intro
      (And.intro p_qr.left p_qr.right.left) p_qr.right.right)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpq_r => Or.elim hpq_r
      (fun hpq => Or.elim hpq
        (fun hp => Or.inl hp)
        (fun hq => Or.inr (Or.inl hq)))
      (fun hr => Or.inr (Or.inr hr)))
    (fun hp_qr => Or.elim hp_qr
      (fun hp => Or.inl (Or.inl hp))
      (fun hqr => Or.elim hqr
        (fun hq => Or.inl (Or.inr hq))
        (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hp_qr => Or.elim hp_qr.right
      (fun hq => Or.inl (And.intro hp_qr.left hq))
      (fun hr => Or.inr (And.intro hp_qr.left hr)))
    (fun hpq_pr => Or.elim hpq_pr
      (fun hpq => And.intro hpq.left (Or.inl hpq.right))
      (fun hpr => And.intro hpr.left (Or.inr hpr.right)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hp_qr => Or.elim hp_qr
      (fun hp => And.intro (Or.inl hp) (Or.inl hp))
      (fun hqr => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (fun hpq_pr => Or.elim hpq_pr.left
      (fun hp => Or.inl hp)
      (fun hq => Or.elim hpq_pr.right
        (fun hp => Or.inl hp)
        (fun hr => Or.inr (And.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hp_q_r: p → (q → r) =>
      fun hpq => (hp_q_r hpq.left hpq.right))
    (fun hpq: p ∧ q → r =>
      fun hp => fun hq => hpq (And.intro hp hq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpq_r: (p ∨ q) → r =>
      And.intro
        (fun hp => hpq_r (Or.inl hp))
        (fun hq => hpq_r (Or.inr hq)))
    (fun hpr_qr: (p → r) ∧ (q → r) =>
      (fun hpq => Or.elim hpq hpr_qr.left hpr_qr.right))

--   example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hnpq: ¬(p ∨ q) => And.intro
      (fun hp => hnpq (Or.inl hp))
      (fun hq => hnpq (Or.inr hq)))
    (fun hnp_nq: ¬p ∧ ¬q =>
      (fun hpq: p ∨ q => hpq.elim
        (fun hp => hnp_nq.left hp)
        (fun hq => hnp_nq.right hq)))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun hnp_nq hpq => Or.elim hnp_nq
    (fun hnp => hnp hpq.left)
    (fun hnq => hnq hpq.right))

example : ¬(p ∧ ¬p) :=
  (fun hp_np => hp_np.right hp_np.left)

example : p ∧ ¬q → ¬(p → q) :=
  (fun hp_nq hpq => hp_nq.right (hpq hp_nq.left))

example : ¬p → (p → q) :=
  (fun hnp hp => False.elim (hnp hp))

example : (¬p ∨ q) → (p → q) :=
  (fun hnp_q hp => Or.elim hnp_q
    (fun hnp => False.elim (hnp hp))
    (fun hq => hq))

example : p ∨ False ↔ p :=
  Iff.intro
    (fun hp_f: p ∨ False => Or.elim hp_f
      (fun hp: p => hp)
      (fun f: False => False.elim f))
    (fun hp: p => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun hpf => hpf.right)
    (fun f => False.elim f)

example : p ∧ False ↔ False :=
  Iff.intro And.right False.elim

example : (p → q) → (¬q → ¬p) :=
  (fun hpq => (fun hnq => fun hp =>
    False.elim (hnq (hpq hp))))

example : (p → q) → (¬q → ¬p) :=
  (fun hpq hnq hp =>
    False.elim (hnq (hpq hp)))

end sect3_7

-- definitions
def succ (x: Nat) := Nat.succ x
theorem add_zero (a: Nat): a + 0 = a := rfl -- "axiom"
theorem add_succ (a b: Nat): a + succ b = succ (a + b) := rfl -- "axiom"
theorem one_eq_succ_zero: 1 = succ 0 := rfl -- "definition"
theorem two_eq_succ_one: 2 = succ 1 := rfl -- "definition"
theorem three_eq_succ_two: 3 = succ 2 := rfl -- "definition"
theorem four_eq_succ_three: 4 = succ 3 := rfl -- "definition"
theorem succ_add : ∀ (n m : Nat), (succ n) + m = succ (n + m)
  | _, 0   => rfl
  | n, m+1 => congrArg succ (succ_add n m)
theorem add_comm : ∀ (n m : Nat), n + m = m + n := by grind

theorem zero_add (a: Nat): 0 + a = a := by
  rw [add_comm, add_zero]
-- end of definitions

-- Level 1 / 8 : The rfl tactic
example (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

-- Level 2 / 8 : the rw tactic
example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

-- Level 3 / 8 : Numbers
example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero]

-- Level 4 / 8 : rewriting backwards
example : 2 = succ (succ 0) := by
  rw [<-one_eq_succ_zero, <- two_eq_succ_one]

-- Level 5 / 8 : Adding zero
example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero, add_zero]

-- Level 6 / 8 : Precision rewriting
example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c, add_zero b]

-- Level 7 / 8 : add_succ
theorem succ_eq_add_one n : succ n = n + 1 := by
  rw [one_eq_succ_zero, add_succ, add_zero]

-- Level 8 / 8 : 2+2=4
example : (2 : Nat) + 2 = 4 := by
  calc (2 : Nat) + 2
    _ = (succ 1) + succ 1 := by rw [two_eq_succ_one]
    _ = succ (1 + succ 1) := by rw [succ_add]
    _ = succ (succ (1 + 1)) := by rw [add_succ]
    _ = succ (succ (succ (succ 0))) := by rw [one_eq_succ_zero, succ_add, zero_add]
    _ = 4 := by rw [<-one_eq_succ_zero, <-two_eq_succ_one, <-three_eq_succ_two, <-four_eq_succ_three]

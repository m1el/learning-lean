theorem foo: 1 = 0 := by sorry

inductive Digit where
  | zero : Digit
  | one  : Digit
deriving Repr

namespace Digit
def addC (a b c: Digit): Digit × Digit := match (a, b, c) with
  | (zero, zero, zero) => (zero, zero)
  | (zero, zero, one )
  | (zero, one,  zero)
  | (one,  zero, zero) => (one,  zero)
  | (zero, one,  one )
  | (one,  zero, one )
  | (one,  one,  zero) => (zero, one )
  | (one,  one,  one ) => (one,  one )

def toNat: (x: Digit) → Nat
  | zero => 0
  | one => 1

-- `addC` is a full adder on single digits: the returned (sum bit, carry) satisfy
-- `sum + 2 * carry = a + b + c`. Checked exhaustively over all 8 inputs.
theorem addC_toNat (a b c : Digit) :
  let (r, c2) := addC a b c;
    r.toNat + 2 * c2.toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

end Digit

inductive BinaryNumber where
  | zero : BinaryNumber
  -- implicit leading 1
  | nonZero : List Digit → BinaryNumber


-- `l` holds the bits *below* an implicit most-significant 1, little-endian
-- (head = least-significant). So the empty list is the number 1 (just the MSB),
-- and `d :: ds` is `d + 2 * ⟦ds⟧`. This represents exactly the naturals ≥ 1.
def listToNat: (l: List Digit) → Nat
  | .nil => 1
  | .cons d ds => d.toNat + 2 * listToNat ds

-- Inverse for n ≥ 1: strip the most-significant 1 and record the lower bits.
-- 1 ↦ [] (nothing below the MSB); n+2 ↦ (low bit) :: bits of (n+2)/2.
def natToList : (x : Nat) → List Digit
  | 0 => .nil          -- 0 is not representable; [] is an arbitrary total-fn value
  | 1 => .nil
  | n + 2 =>
    let m := n + 2
    let d : Digit := if m % 2 == 0 then .zero else .one
    d :: natToList (m / 2)

theorem two_way_list : ∀ n : Nat, 0 < n → listToNat (natToList n) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    match n, hn with
    | 1, _ => simp [natToList, listToNat]
    | k + 2, _ =>
      -- ih on (k+2)/2, which is ≥ 1 and < k+2
      have ihm := ih ((k + 2) / 2) (by omega) (by omega)
      -- unfold `natToList` on n+2 (→ `d :: rest`) and `listToNat` on the cons,
      -- feed in the recursive result, then case on the parity bit and do arith
      simp only [natToList, listToNat]
      rw [ihm]
      rcases Nat.mod_two_eq_zero_or_one (k + 2) with h | h <;>
        simp [h, Digit.toNat] <;> omega

-- `nonZero l` is the number whose lower bits (below the implicit MSB) are `l`.
def BinaryNumber.toNat: (x: BinaryNumber) → Nat
  | .zero => .zero
  | .nonZero l => listToNat l
def BinaryNumber.ofNat: (x: Nat) → BinaryNumber
  | .zero => .zero
  | n => .nonZero (natToList n)

-- `ofNat` is a section of `toNat` on the positive naturals (from `two_way_list`).
theorem BinaryNumber.toNat_ofNat : ∀ n, 0 < n → (BinaryNumber.ofNat n).toNat = n := by
  intro n hn
  match n, hn with
  | k + 1, _ => exact two_way_list (k + 1) (by omega)

-- Add a carry to a single MSB-implicit number, in place (no Nat round-trip):
-- `incList zero l = l`, and carrying `one` ripples through the lower bits and,
-- when it reaches the implicit MSB (empty list = value 1), turns 1 into 2 = [0].
def incList : Digit → List Digit → List Digit
  | .zero, l => l
  | .one, .nil => [.zero]
  | .one, a :: as =>
    let (s, c2) := Digit.addC a .zero .one
    s :: incList c2 as

theorem incList_listToNat (c : Digit) (l : List Digit) :
    listToNat (incList c l) = listToNat l + c.toNat := by
  induction c, l using incList.induct with
  | case1 l => simp [incList, Digit.toNat]
  | case2 => simp [incList, listToNat, Digit.toNat]
  | case3 a as s c2 heq ih =>
      have h2 := Digit.addC_toNat a .zero .one; rw [heq] at h2
      simp only [incList, heq, listToNat, Digit.toNat] at *; omega

-- Ripple-carry adder directly on the MSB-implicit lists. When one operand runs
-- out, its implicit MSB (1) is added at that position and the remaining carry is
-- rippled through the other operand via `incList`. When both run out, their two
-- implicit MSBs plus the carry give `1 + 1 + c`, i.e. the list `[c]` (value 2+c).
def addList (c : Digit) : List Digit → List Digit → List Digit
  | .nil, .nil => [c]
  | .cons a as, .nil
  | .nil, .cons a as =>
    let (s, c2) := Digit.addC a .one c
    .cons s (incList c2 as)
  | .cons a as, .cons b bs =>
    let (s, c2) := Digit.addC a b c
    .cons s (addList c2 as bs)

-- addList corresponds to Nat addition: the value of the result is the sum of the
-- operand values plus the carry-in. Proved by functional induction on `addList`,
-- each step discharged by the digit full-adder lemma `Digit.addC_toNat`.
theorem addList_listToNat (c : Digit) (a b : List Digit) :
    listToNat (addList c a b) = listToNat a + listToNat b + c.toNat := by
  induction c, a, b using addList.induct with
  | case1 c => cases c <;> simp [addList, listToNat, Digit.toNat]
  | case2 c a as s c2 heq
  | case3 c a as s c2 heq =>
      have h2 := Digit.addC_toNat a .one c; rw [heq] at h2
      simp only [addList, heq, listToNat, incList_listToNat, Digit.toNat] at *; omega
  | case4 c a as b bs s c2 heq ih =>
      have h2 := Digit.addC_toNat a b c; rw [heq] at h2
      simp only [addList, heq, listToNat] at *; omega

def BinaryNumber.add: (a b: BinaryNumber) → BinaryNumber
  | .zero, b => b
  | a, .zero => a
  | .nonZero a, .nonZero b => .nonZero (addList .zero a b)

instance : Add BinaryNumber where add := BinaryNumber.add

-- End-to-end: BinaryNumber addition agrees with Nat addition.
theorem BinaryNumber.add_toNat (a b : BinaryNumber) :
    (a + b).toNat = a.toNat + b.toNat := by
  show (BinaryNumber.add a b).toNat = a.toNat + b.toNat
  match a, b with
  | .zero, b
  | .nonZero a, .zero => simp [BinaryNumber.add, BinaryNumber.toNat]
  | .nonZero a, .nonZero b =>
    show listToNat (addList .zero a b) = listToNat a + listToNat b
    rw [addList_listToNat]; simp [Digit.toNat]

def a: BinaryNumber := .nonZero .nil
def b: BinaryNumber := .nonZero (.cons .one .nil)

#eval (a.toNat + b.toNat, (a + b).toNat)

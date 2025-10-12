import Mathlib

lemma one_eq_succ_zero :
  1 = Nat.succ 0 := by
  rfl

lemma two_eq_succ_one :
  2 = Nat.succ 1 := by
  rfl


example (x : Nat) (h : x = Nat.succ 0) :
  x = 1 := by
  rw [one_eq_succ_zero] -- Actually, this line can be ommitted.
  exact h



example :
  42=42 := by
  rfl

example (x y : Nat) (h : y = x + 7) :
  2 * y = 2 * (x + 7) := by
  rw [h]

example :
  2 = (Nat.succ 0).succ := by
  rfl

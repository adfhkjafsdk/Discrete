import Mathlib

def my_add (a b : ℕ) :=
  a + b

example (a b : ℕ) :
  my_add a b = b+a := by
  rw [my_add]
  rw [add_comm]

#eval my_add 20 30

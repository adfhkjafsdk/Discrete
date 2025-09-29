import Mathlib

example (P : Prop) :
  (P↔ P) := by
  rfl

example (P : Prop) :
  (False∨P)↔P := by
  rw [false_or]


-- example (P : Prop) :
--   (P∧¬P) ↔ False := by
--   rw [← @not_not (P∧¬P)]
--   apply [@and_not_self P]

example (P : Prop) :
  (P∧¬P) ↔ False := by
  rw [and_not_self_iff]

example (P : Prop) :
  (P∨¬P)↔True := by
  rw [or_iff_not_imp_left]
  rw [imp_self]

example (P : Prop) : P ∨ ¬P ↔ True := by
  have h1 : P ∨ ¬P := by
    apply em
  constructor
  · -- Assume P ∨ ¬P, prove True
    intro h
    trivial
  · -- Assume True, prove P ∨ ¬P
    intro h
    exact h1

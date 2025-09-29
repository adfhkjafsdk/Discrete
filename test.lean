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

example (P : Prop) :
  (¬P)↔(P→False) := by
  apply Iff.intro
  · -- Assume ¬P, prove P→False
    intro h1 h2
    contradiction
  · -- Assume P→False, prove ¬P
    intro h1 h2
    apply h1
    exact h2


lemma iff_not_self_iff_false (P : Prop) :
  (P↔¬P)↔False := by
  rw [@iff_iff_implies_and_implies P (¬P)]
  nth_rw 4 [← @not_not P]
  repeat rw [imp_not_self]
  rw [and_not_self_iff]

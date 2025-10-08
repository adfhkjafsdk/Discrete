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

theorem exercise_2_1_4 (P Q : Prop) :
  ((P↔Q)↔((P∧¬Q)∨(Q∧¬P))) ↔ (P∧¬P) := by
  rw [← @not_not (P∧¬Q),← @not_not (Q∧¬P)]
  rw [← not_and_or]
  rw [@not_and_or P (¬Q), @not_and_or Q (¬P)]
  repeat rw [not_not]
  repeat rw [← imp_iff_not_or]
  rw [← iff_iff_implies_and_implies]
  have iff_not_self_iff_false (P : Prop) : (P↔¬P)↔False := by
    rw [@iff_iff_implies_and_implies P (¬P)]
    nth_rw 4 [← @not_not P]
    repeat rw [imp_not_self]
    rw [and_not_self_iff]
  -- have iii (P : Prop) : ¬(P↔¬P):= iff_not_self
  -- rw [← @false_iff (P↔Q)] at iii
  -- rw [← @iii (P ↔ Q)]
  -- have iii (P : Prop) := iff_not_self P
  rw [iff_not_self_iff_false]
  rw [and_not_self_iff]

theorem test0 (P Q : Prop) (h1 : P) (h2 : Q) :
  P∧Q := by
  apply And.intro
  · exact h1
  · exact h2

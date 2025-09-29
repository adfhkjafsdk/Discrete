import Mathlib

theorem example_1_4_2_1 (R S : Prop) :
  (R∨S)∨¬(R∨S) := by
  apply Classical.em

theorem example_1_4_2_2 (R S P Q : Prop) :
  ((R∨S)∧((R∨S)→(P∨Q)))→(P∨Q) := by
  intro h
  exact h.right h.left

theorem exercise_1_4_1 (P : Prop) :
  P→P := by
  intro h
  exact h

theorem exercise_1_4_2 (P Q : Prop) :
  ¬¬((P∨Q)→(Q∨P)) := by
  rw [not_not]
  intro h
  rw [or_comm]
  exact h

theorem exercise_1_4_3 (P Q R : Prop) :
  (Q→R)→((P∨Q)→(P∨R)) := by
  intro h1 h2
  cases h2 with
  | inl h2l =>
    apply Or.intro_left
    exact h2l
  | inr h2r =>
    apply Or.intro_right
    apply h1
    exact h2r

theorem exercise_1_4_4 (P Q R : Prop) :
  (Q→R)→((P→Q)→(P→R)) := by
  intro h1 h2 h3
  apply h1
  apply h2
  exact h3

theorem exercise_1_4_5 (P Q : Prop) :
  (P→Q)→(¬Q→¬P) := by
  intro h
  rw [imp_iff_not_or, or_comm, ← @not_not Q] at h
  rw [← imp_iff_not_or] at h
  exact h

theorem exercise_1_4_6 (P Q : Prop) :
  (P∧Q)→(P∨Q) := by
  intro h
  apply Or.intro_left
  exact h.left

theorem example_2_1_1_1 (P Q : Prop) :
  (P∧¬P)∨Q ↔ Q := by
  rw [and_not_self_iff]
  rw [false_or]

theorem example_2_1_1_2 (P Q : Prop) :
  (P∨¬P) ↔ (Q∨¬Q) := by
  rw [or_iff_not_imp_left, or_iff_not_imp_left]
  rw [imp_self, imp_self]

theorem example_2_2_4_1 (P Q R : Prop) :
  (¬P∧(¬Q∧R))∨(Q∧R)∨(P∧R) ↔ R := by
  rw [← and_assoc]
  rw [← or_and_right, ← or_and_right]
  rw [← not_or]
  nth_rw 1 [@or_comm Q P]
  rw [or_iff_not_imp_left, not_not, imp_self]
  rw [true_and]

theorem example_2_2_4_2 (P Q R : Prop) :
  ((P∨Q)∧¬(¬P∧(¬Q∨¬R)))∨(¬P∧¬Q)∨(¬P∧¬R) ↔ True := by
  repeat rw [← not_and_or]
  repeat rw [← not_or]
  rw [not_not]
  rw [← or_and_left]
  rw [← and_assoc, and_self_iff]
  rw [← not_and_or]
  rw [← or_and_left]
  rw [or_iff_not_imp_left, imp_self]

theorem exercise_2_1_1 (P Q R : Prop) :
  P→(Q∧R) ↔ (P→Q)∧(P→R) := by
  repeat rw [imp_iff_not_or]
  rw [or_and_left]

theorem exercise_2_1_2 (P Q : Prop) :
  P→Q ↔ ¬Q→¬P := by
  repeat rw [imp_iff_not_or]
  rw [@not_not Q, or_comm]

theorem exercise_2_1_3 (P Q R : Prop) :
  ((P→¬Q)→(Q→¬P))∧R ↔ R := by
  repeat rw [imp_iff_not_or]
  rw [@or_comm (¬P) (¬Q)]
  rw [or_comm, or_iff_not_imp_left, imp_self]
  rw [true_and]

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
  rw [iff_not_self_iff_false]
  rw [and_not_self_iff]

theorem exercise_2_1_5 (P Q R : Prop) :
  P→(Q→R) ↔ (P∧Q)→R := by
  rw [imp_iff_not_or, imp_iff_not_or, ← or_assoc]
  rw [← not_and_or]
  rw [← imp_iff_not_or]

theorem exercise_2_1_6 (P Q : Prop) :
  ¬(P↔Q) ↔ (P∧¬Q)∨(¬P∧Q) := by
  rw [@iff_iff_implies_and_implies P Q]
  rw [imp_iff_not_or, imp_iff_not_or]
  rw [not_and_or]
  repeat rw [not_or, not_not]
  rw [@and_comm Q (¬P)]

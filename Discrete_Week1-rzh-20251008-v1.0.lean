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

theorem my_and_comm (P Q : Prop) :
  P∧Q ↔ Q∧P := by
  apply Iff.intro
  · intro h
    apply And.intro
    · exact h.right
    · exact h.left
  · intro h
    apply And.intro
    · exact h.right
    · exact h.left

theorem my_and_assoc (P Q R : Prop) :
  (P∧Q)∧R ↔ P∧(Q∧R) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · exact h.left.left
    · apply And.intro
      · exact h.left.right
      · exact h.right
  · intro h
    apply And.intro
    · apply And.intro
      · exact h.left
      · exact h.right.left
    · exact h.right.right

theorem my_or_comm (P Q : Prop) :
  P∨Q ↔ Q∨P := by
  apply Iff.intro
  · intro h
    cases h with
      | inl hl =>
        apply Or.intro_right
        exact hl
      | inr hr =>
        apply Or.intro_left
        exact hr
  · intro h
    cases h with
      | inl hl =>
        apply Or.intro_right
        exact hl
      | inr hr =>
        apply Or.intro_left
        exact hr

theorem my_or_assoc (P Q R : Prop) :
  (P∨Q)∨R ↔ P∨(Q∨R) := by
  apply Iff.intro
  · intro h
    cases h with
      | inl hl =>
        cases hl with
        | inl hll =>
          apply Or.intro_left
          exact hll
        | inr hlr =>
          apply Or.intro_right
          apply Or.intro_left
          exact hlr
      | inr hr =>
        repeat apply Or.intro_right
        exact hr
  · intro h
    cases h with
      | inl hl =>
        repeat apply Or.intro_left
        exact hl
      | inr hr =>
        cases hr with
        | inl hrl =>
          apply Or.intro_left
          apply Or.intro_right
          exact hrl
        | inr hrr =>
          apply Or.intro_right
          exact hrr

theorem my_not_and_or (P Q : Prop) :
  ¬(P∧Q) ↔ ¬P∨¬Q := by
  by_cases h: P
  · rw [← @iff_true P] at h
    rw [h, not_true, true_and, false_or]
  · rw [← @iff_false P] at h
    rw [h, not_false_iff, false_and, true_or, not_false_iff]

theorem my_not_or (P Q : Prop) :
  ¬(P∨Q) ↔ ¬P∧¬Q := by
  by_cases h: P
  · rw [← @iff_true P] at h
    rw [h, not_true, true_or, false_and, not_true]
  · rw [← @iff_false P] at h
    rw [h, not_false_iff, false_or, true_and]


-- Homework

example (Q S E U : Prop)
  (h1 : ¬Q ∨ S) (h2 : (E → ¬U) → ¬S) :
  Q → E := by
  rw [← imp_iff_not_or] at h1
  rw [← not_imp_not, not_not] at h2
  rw [@imp_iff_not_or E ¬U, not_or, not_not, not_not] at h2
  intro h
  apply h1 at h
  apply h2 at h
  exact h.left

example (P Q R S : Prop)
  (h1 : ¬P → Q) (h2 : Q → ¬R) (h3 : (R ∧ ¬S) ∨ (¬R ∧ S)) (h4 : ¬S) :
  P := by
  have h12 : ¬P→¬R := by
    intro h0
    apply h2
    apply h1
    exact h0
  rw [not_imp_not] at h12
  apply Or.intro_right R at h4
  rw [or_comm] at h3
  nth_rw 1 [← @not_not S] at h3
  rw [← not_or, ← imp_iff_not_or] at h3
  apply h3 at h4
  apply h12
  exact h4.left

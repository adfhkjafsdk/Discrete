import Mathlib

variable {P Q R S : Prop}

theorem thm281_1 (h : P ∧ Q) :
  P := h.left

theorem thm281_2 (h : ¬(P→Q)) :
  P := by
  rw [imp_iff_not_or, not_or, not_not] at h
  exact h.left

theorem thm281_3 (h : ¬(P→Q)) :
  ¬Q := by
  rw [imp_iff_not_or, not_or, not_not] at h
  exact h.right

theorem thm281_4 (h : P) :
  P∨Q := by
  apply Or.intro_left
  exact h

theorem thm281_5 (h : ¬P) :
  P→Q := by
  intro hp
  contradiction

theorem thm281_6 (h : Q) :
  P→Q := by
  intro _
  exact h

theorem thm281_7 (h : ¬P ∧ (P ∨ Q)) :
  Q := by
  have hr : P∨Q := h.right
  rw [← @not_not P, ← imp_iff_not_or ] at hr
  apply hr h.left

theorem thm281_8 (h : P ∧ (P → Q)) :
  Q := h.right h.left

theorem thm281_9 (h : ¬Q ∧ (P → Q)) :
  ¬P := by
  have hr : P→Q := h.right
  rw [← not_imp_not] at hr
  exact hr h.left

theorem thm281_10 (h : (P → Q) ∧ (Q → R)) :
  P→R := by
  intro hp
  exact h.right (h.left hp)

theorem thm281_11 (h : (P ↔ Q) ∧ (Q ↔ R)) :
  P↔R := by
  rw [h.left, h.right]

theorem thm281_12 (h : (P → R) ∧ (Q → R) ∧ (P ∨ Q)) :
  R := by
  cases h.right.right with
    | inl hp => exact h.left hp
    | inr hq => exact h.right.left hq

theorem thm281_13 (h : (P → Q) ∧ (R → S) ∧ (P ∨ R)) :
  Q ∨ S := by
  rcases h with ⟨h1, h2, h3⟩
  cases h3 with
    | inl hp =>
      apply Or.intro_left
      exact h1 hp
    | inr hq =>
      apply Or.intro_right
      exact h2 hq

theorem thm281_14 (h : (P → Q) ∧ (R → S) ∧ (¬Q ∨ ¬S)) :
  ¬P ∨ ¬R := by
  rw [← imp_iff_not_or]
  rw [← imp_iff_not_or, ← @not_imp_not S R] at h
  intro hp
  rcases h with ⟨h1, h2, h3⟩
  exact h2 (h3 (h1 hp))

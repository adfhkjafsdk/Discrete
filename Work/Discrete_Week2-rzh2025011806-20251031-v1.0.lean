import Mathlib

-- variable {P Q R S : Prop}

theorem thm281_1 (P Q : Prop) (h : P ∧ Q) :
  P := h.left

theorem thm281_2 (P Q : Prop) (h : ¬(P→Q)) :
  P := by
  rw [imp_iff_not_or, not_or, not_not] at h
  exact h.left

theorem thm281_3 (P Q : Prop) (h : ¬(P→Q)) :
  ¬Q := by
  rw [imp_iff_not_or, not_or, not_not] at h
  exact h.right

theorem thm281_4 (P Q : Prop) (h : P) :
  P∨Q := by
  apply Or.intro_left
  exact h

theorem thm281_5 (P Q : Prop) (h : ¬P) :
  P→Q := by
  intro hp
  contradiction

theorem thm281_6 (P Q : Prop) (h : Q) :
  P→Q := by
  intro _
  exact h

theorem thm281_7 (P Q : Prop) (h : ¬P ∧ (P ∨ Q)) :
  Q := by
  have hr : P∨Q := h.right
  rw [← @not_not P, ← imp_iff_not_or ] at hr
  apply hr h.left

theorem thm281_8 (P Q : Prop) (h : P ∧ (P → Q)) :
  Q := h.right h.left

theorem thm281_9 (P Q : Prop) (h : ¬Q ∧ (P → Q)) :
  ¬P := by
  have hr : P→Q := h.right
  rw [← not_imp_not] at hr
  exact hr h.left

theorem thm281_10 (P Q R : Prop) (h : (P → Q) ∧ (Q → R)) :
  P→R := by
  intro hp
  exact h.right (h.left hp)

theorem thm281_11 (P Q R : Prop) (h : (P ↔ Q) ∧ (Q ↔ R)) :
  P↔R := by
  rw [h.left, h.right]

theorem thm281_12 (P Q R : Prop) (h : (P → R) ∧ (Q → R) ∧ (P ∨ Q)) :
  R := by
  cases h.right.right with
    | inl hp => exact h.left hp
    | inr hq => exact h.right.left hq

theorem thm281_13 (P Q R S : Prop) (h : (P → Q) ∧ (R → S) ∧ (P ∨ R)) :
  Q ∨ S := by
  rcases h with ⟨h1, h2, h3⟩
  cases h3 with
    | inl hp => exact Or.intro_left S (h1 hp)
    | inr hq => exact Or.intro_right Q (h2 hq)

theorem thm281_14 (P Q R S : Prop) (h : (P → Q) ∧ (R → S) ∧ (¬Q ∨ ¬S)) :
  ¬P ∨ ¬R := by
  rw [← imp_iff_not_or]
  rw [← imp_iff_not_or, ← @not_imp_not S R] at h
  intro hp
  rcases h with ⟨h1, h2, h3⟩
  exact h2 (h3 (h1 hp))

theorem thm281_15 (P Q R : Prop) (h : Q → R) :
  (P∨Q)→(P∨R) := by
  intro hh
  cases hh with
    | inl hp => exact Or.intro_left R hp
    | inr hq => exact Or.intro_right P (h hq)

theorem thm281_16 (P Q R : Prop) (h : Q → R) :
  (P→Q)→(P→R) := by
  intro hpq hp
  exact h (hpq hp)

theorem thm292_1 (P Q R : Prop) (h : (P → Q) ∧ (Q → R) ∧ P) :
  R := by
  rcases h with ⟨hpq, hqr, hp⟩
  exact hqr (hpq hp)

theorem thm292_2 (A B C D E R S : Prop)
  (h : (C ∨ D) ∧ ((C ∨ D) → ¬E) ∧ (¬E → (A ∧ ¬B)) ∧ ((A ∧ ¬B) → (R ∨ S))) :
  R ∨ S := by
  rcases h with ⟨hcd, hcd_ne, hne_anb, hanb_rs⟩
  exact hanb_rs (hne_anb (hcd_ne hcd))

theorem thm292_3 (P Q R S : Prop)
  (h : (P ∧ Q) ∧ (P → R) ∧ (Q → S)) :
  S ∨ R := by
  rcases h with ⟨hpq, hpr, hqs⟩
  have h0 : S ∧ R :=
    And.intro (hqs hpq.right) (hpr hpq.left)
  apply Or.intro_left
  exact h0.left

theorem thm292_4 (P Q R S : Prop)
  (h : (P → (Q → S)) ∧ (¬R ∨ P) ∧ Q) :
  R → S := by
  rcases h with ⟨hpqs, hrp, hq⟩
  rw [← imp_iff_not_or] at hrp
  intro hr
  exact hpqs (hrp hr) hq

theorem thm292_5 (P Q R S : Prop)
  (h : (¬(P → Q) → ¬(R ∨ S)) ∧ ((Q → P) ∨ ¬R) ∧ R) :
  P ↔ Q := by
  rcases h with ⟨h1, h2, h3⟩
  rw [or_comm, ← imp_iff_not_or] at h2
  rw [not_imp_not] at h1
  have h4 : P→Q := h1 (Or.intro_left S h3)
  apply Iff.intro
  · intro hp
    exact h4 hp
  · intro hq
    exact (h2 h3) hq

theorem exercise_2_7_1 (P Q R : Prop)
  (h : (P → Q)) :
  ((P ∧ R) → Q) := by
  intro hl
  exact h hl.left

theorem exercise_2_7_2 (P Q R : Prop)
  (h : (P → Q)) :
  (P → (Q ∨ R)) := by
  intro hp
  exact Or.intro_left R (h hp)

theorem exercise_2_7_8 (P Q : Prop)
  (h : (P ∧ Q) ∨ (P → Q)) :
  (P → Q) := by
  rw [imp_iff_not_or] at h
  rw [@or_comm (¬P) Q, ← or_assoc, @or_comm (P∧Q) Q] at h
  rw [or_and_left, or_self] at h
  rw [or_comm, ← imp_iff_not_or] at h
  intro hp
  exact (h hp).right



-- 归结推理
theorem resolution_general (P Γ Δ : Prop)
  (h1 : ¬P ∨ Γ) (h2 : P ∨ Δ) : Γ ∨ Δ := by
  cases h1 with
  | inl h_not_p =>
    cases h2 with
    | inl h_p => exact (h_not_p h_p).elim
    | inr hΔ  => exact Or.inr hΔ
  | inr hΓ =>
    exact Or.inl hΓ

lemma resolution_general_l (P Γ : Prop)
  (h1 : ¬P ∨ Γ) (h2 : P) : Γ := by
  rw [← @or_false P] at h2
  rw [← @or_false Γ]
  exact resolution_general P Γ False h1 h2

lemma resolution_general_r (P Δ : Prop)
  (h1 : ¬P) (h2 : P ∨ Δ) : Δ := by
  rw [← @or_false ¬P] at h1
  rw [← @false_or Δ]
  exact resolution_general P False Δ h1 h2

lemma resolution_general_same (P Δ : Prop)
  (h1 : ¬P ∨ Δ) (h2 : P ∨ Δ) : Δ := by
  rw [← @or_self Δ]
  exact resolution_general P Δ Δ h1 h2

theorem thm2_10_2_1 (P Q : Prop) -- Using resolution general
  (h : (P → Q) ∧ P) : Q := by
  repeat rw [imp_iff_not_or] at h
  rcases h with ⟨h1, h2⟩
  apply resolution_general_l P Q h1 h2

theorem thm2_10_2_2 (P Q R : Prop) -- Using resolution general
  (h : (P → Q) ∧ (Q → R)) : (P → R) := by
  repeat rw [imp_iff_not_or] at h
  repeat rw [imp_iff_not_or]
  rcases h with ⟨h1, h2⟩
  rw [or_comm] at h1
  rw [or_comm]
  apply resolution_general Q R (¬P) h2 h1

theorem exercise2_12_1 (P Q R : Prop) -- Using resolution general
  (h : (P ∨ Q) ∧ (P → R) ∧ (Q → R)) : R := by
  repeat rw [imp_iff_not_or] at h
  rcases h with ⟨h1, h2, h3⟩
  have h4 : R ∨ Q :=
    resolution_general P R Q h2 h1
  rw [or_comm] at h4
  exact resolution_general_same Q R h3 h4

theorem exercise2_12_2 (P Q R S : Prop) -- Using resolution general
  (h : (S → ¬Q) ∧ (P → Q) ∧ (R ∨ S) ∧ (R → ¬Q)) : ¬P := by
  repeat rw [imp_iff_not_or] at h
  rcases h with ⟨h1, h2, h3, h4⟩
  have h5 : ¬Q ∨ S :=
    resolution_general R (¬Q) S h4 h3
  rw [or_comm] at h5
  have h6 : ¬Q  :=
    resolution_general_same S (¬Q) h1 h5
  rw [or_comm] at h2
  exact resolution_general_r Q (¬P) h6 h2

theorem exercise2_12_3 (P Q R : Prop) -- Using resolution general
  (h : ¬(P ∧ ¬Q) ∧ (¬Q ∨ R) ∧ ¬R) : ¬P := by
  repeat rw [not_and_or, not_not] at h
  rcases h with ⟨h1, h2, h3⟩
  rw [or_comm] at h1
  have h4 : R ∨ ¬P :=
    resolution_general Q R (¬P) h2 h1
  exact resolution_general_r R (¬P) h3 h4


--- Russell

axiom axiom1 (P : Prop) : (P ∨ P) → P
axiom axiom2 (P Q : Prop) : P → (P ∨ Q)
axiom axiom3 (P Q : Prop) : (P ∨ Q) → (Q ∨ P)
axiom axiom4 (P Q R : Prop) : (Q → R) → ((P ∨ Q) → (P ∨ R))

axiom def1 (P Q : Prop) : (P → Q) = (¬P ∨ Q)
axiom def2 (P Q : Prop) : (P ∧ Q) = ¬(¬P ∨ ¬Q)
axiom def3 (P Q : Prop) : (P ↔ Q) = (P → Q) ∧ (Q → P)

theorem thm326_1 (P Q R : Prop) :
  (Q → R) → ((P → Q) → (P → R)) := by
  have step1 : (Q → R) → ((¬P ∨ Q) → (¬P ∨ R)) := axiom4 (¬P) Q R
  rw [← def1] at step1  -- (Q → R) → ((P → Q) → (¬P ∨ R))
  rw [← def1] at step1  -- Q → R) → ((P → Q) → (P → R))
  exact step1

theorem thm326_2 (P : Prop) :
  (P → P) := by
  have step1 : (P ∨ P) → P := axiom1 P
  have step2 : P → (P ∨ P) := axiom2 P P
  have step3 : ((P∨P)→P) → ((P→(P∨P)) → (P→P)) := thm326_1 P (P∨P) P
  have step4 : (P→(P∨P)) → (P→P) := step3 step1
  exact step4 step2

theorem thm326_3 (P : Prop) :
  ¬P ∨ P := by
  have step1 : P → P := thm326_2 P
  rw [def1] at step1  -- ¬P ∨ P
  exact step1

theorem thm326_4 (P : Prop) :
  P ∨ ¬P := by
  have step1 : ¬P ∨ P := thm326_3 P
  have step2 : (¬P∨P)→(P∨¬P) := axiom3 (¬P) P
  exact step2 step1

theorem thm326_5 (P : Prop) :
  P → ¬¬P := by
  have step1 : ¬P∨¬¬P := thm326_4 (¬P)
  rw [← def1] at step1   -- P → ¬¬P
  exact step1

theorem thm326_6 (P : Prop) :
  ¬¬P → P := by
  have step1 : ¬P → ¬¬¬P := thm326_5 (¬P)
  have step2 : (¬P→¬¬¬P) → ((P∨¬P)→(P∨¬¬¬P)) := axiom4 P (¬P) (¬¬¬P)
  have step3 : (P∨¬P)→(P∨¬¬¬P) := step2 step1
  have step4 : P∨¬P := thm326_4 P
  have step5 : P∨¬¬¬P := step3 step4
  have step6 : (P∨¬¬¬P)→(¬¬¬P∨P) := axiom3 P (¬¬¬P)
  have step7 : ¬¬¬P∨P := step6 step5
  rw [← def1] at step7   -- ¬¬P → P
  exact step7

theorem thm326_7 (P Q : Prop) :
  (P→Q) → (¬Q → ¬P) := by
  have step1 : Q→¬¬Q := thm326_5 Q
  have step2 : (Q→¬¬Q) → ((¬P∨Q)→(¬P∨¬¬Q)) := axiom4 (¬P) Q (¬¬Q)
  have step3 : (¬P∨Q)→(¬P∨¬¬Q) := step2 step1
  have step4 : (¬P∨¬¬Q → ¬¬Q∨¬P) → ((¬P∨Q → ¬P∨¬¬Q) → (¬P∨Q → ¬¬Q∨¬P)) :=
    thm326_1 (¬P∨Q) (¬P∨¬¬Q) (¬¬Q∨¬P)
  have step5 : ¬P∨¬¬Q → ¬¬Q∨¬P := axiom3 (¬P) (¬¬Q)
  have step6 : (¬P∨Q → ¬P∨¬¬Q) → (¬P∨Q → ¬¬Q∨¬P) := step4 step5
  have step7 : ¬P∨Q → ¬¬Q∨¬P := step6 step3
  rw [← def1] at step7   -- (P → Q) → ¬¬Q ∨ ¬P
  rw [← def1] at step7   -- (P → Q) → ¬Q → ¬P
  exact step7

theorem exercise3_1_1 (P Q : Prop) :
  ¬(P∧Q) → (¬P∨¬Q) := by
  have step1 : ¬¬(¬P∨¬Q) → (¬P∨¬Q) := thm326_6 (¬P∨¬Q)
  rw [← def2] at step1  -- ¬(P ∧ Q) → ¬P ∨ ¬Q
  exact step1

theorem exercise3_1_2 (P Q : Prop) :
  (¬P∨¬Q) → ¬(P∧Q) := by
  have step1 : (¬P∨¬Q) → ¬¬(¬P∨¬Q) := thm326_5 (¬P∨¬Q)
  rw [← def2] at step1  -- ¬P ∨ ¬Q → ¬(P ∧ Q)
  exact step1

theorem exercise3_1_3 (P Q : Prop) :
  P→(Q∨P) := by
  have step1 : (P∨Q)→(Q∨P) := axiom3 P Q
  have step2 : (P∨Q → Q∨P) → ((P → P∨Q) → (P → Q∨P)) := thm326_1 P (P∨Q) (Q∨P)
  have step3 : (P → P∨Q) → (P → Q∨P) := step2 step1
  have step4 : P → P∨Q := axiom2 P Q
  exact step3 step4

theorem exercise3_1_4 (P Q : Prop) :
  Q→(P→Q) := by
  have step1 : Q→(¬P∨Q) := exercise3_1_3 Q (¬P)
  rw [← def1] at step1  -- Q → (P → Q)
  exact step1

theorem russell_ex1 (P Q : Prop) :
  P∧Q → Q := by
  have step1 : ((¬Q)∨(¬P))→((¬P)∨(¬Q)) := axiom3 (¬Q) (¬P)
  have step2 : ((¬Q)∨(¬P) → (¬P)∨(¬Q)) → (((¬Q) → (¬Q)∨(¬P)) → ((¬Q) → (¬P)∨(¬Q))) :=
    thm326_1 (¬Q) ((¬Q)∨(¬P)) ((¬P)∨(¬Q))
  have step3 : ((¬Q) → (¬Q)∨(¬P)) → ((¬Q) → (¬P)∨(¬Q)) := step2 step1
  have step4 : (¬Q) → (¬Q)∨(¬P) := axiom2 (¬Q) (¬P)
  have step5 : (¬Q) → (¬P∨¬Q) := step3 step4
  have step6 : (¬P∨¬Q → ¬¬(¬P∨¬Q)) → (((¬Q) → (¬P∨¬Q)) → (¬Q → ¬¬(¬P∨¬Q))) :=
    thm326_1 (¬Q) (¬P∨¬Q) (¬¬(¬P∨¬Q))
  have step7 : ¬P∨¬Q → ¬¬(¬P∨¬Q) := thm326_5 (¬P∨¬Q)
  have step8 : ((¬Q) → (¬P∨¬Q)) → (¬Q → ¬¬(¬P∨¬Q)) :=
    step6 step7
  have step9 : ¬Q → ¬¬(¬P∨¬Q) := step8 step5
  have step10 : (¬¬(¬P∨¬Q)→(¬P∨¬Q)) → ((¬Q → ¬¬(¬P∨¬Q)) → (¬Q→(¬P∨¬Q))) :=
    thm326_1 (¬Q) (¬¬(¬P∨¬Q)) (¬P∨¬Q)
  have step11 : ¬¬(¬P∨¬Q)→(¬P∨¬Q) := thm326_6 (¬P∨¬Q)
  have step12 : (¬Q → ¬¬(¬P∨¬Q)) → (¬Q→(¬P∨¬Q)) := step10 step11
  have step13 : ¬Q→(¬P∨¬Q) := step12 step9
  have step14 : (¬Q→(¬P∨¬Q))→(¬(¬P∨¬Q)→¬¬Q) := thm326_7 (¬Q) (¬P∨¬Q)
  have step15 : ¬(¬P∨¬Q)→¬¬Q := step14 step13
  have step16 : (¬¬Q→Q) → ((¬(¬P∨¬Q)→¬¬Q)→(¬(¬P∨¬Q)→Q)) := thm326_1 (¬(¬P∨¬Q)) (¬¬Q) Q
  have step17 : ¬¬Q→Q := thm326_6 Q
  have step18 : (¬(¬P∨¬Q)→¬¬Q)→(¬(¬P∨¬Q)→Q) := step16 step17
  have step19 : ¬(¬P∨¬Q)→Q := step18 step15
  rw [← def2] at step19   -- P ∧ Q → Q
  exact step19

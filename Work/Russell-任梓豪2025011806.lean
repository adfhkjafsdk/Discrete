import Mathlib

-- variable {P Q R : Prop}

axiom axiom1 (P : Prop) : (P∨P)→P
axiom axiom2 (P Q : Prop) : P→(P∨Q)
axiom axiom3 (P Q : Prop) : (P∨Q)→(Q∨P)
axiom axiom4 (P Q R : Prop) : (Q→R)→((P∨Q)→(P∨R))

axiom def1 (A B : Prop) : (A → B) = (¬A ∨ B)
axiom def2 (A B : Prop) : (A ∧ B) = ¬(¬A ∨ ¬B)
axiom def3 (A B : Prop) : (A ↔ B) = ((A → B) ∧ (B → A))

theorem thm_321 (P Q R : Prop) :
  (Q→R)→((P→Q)→(P→R)) := by
  have step1 (P Q R : Prop) : (Q→R)→((P∨Q)→(P∨R)) := axiom4 P Q R
  have step2 : (Q→R)→((¬P∨Q)→(¬P∨R)) := step1 (¬P) Q R
  rw [← @def1 P Q] at step2
  rw [← @def1 P R] at step2
  exact step2

theorem thm_322 (P : Prop) :
  P→P := by
  have step1 (P Q : Prop) : (P→(P∨Q)) := axiom2 P Q
  have step2 : P→(P∨P) := step1 P P
  have step3 : (P∨P)→P := axiom1 P
  have step4 : ((P∨P)→P) → ((P→(P∨P)) → (P→P)) := thm_321 P (P∨P) P
  have step5 : (P→(P∨P)) → (P→P) := step4 step3
  exact step5 step2

theorem thm_323 (P : Prop) :
  ¬P∨P := by
  have step1 : P→P := thm_322 P
  rw [def1] at step1
  exact step1

theorem thm_324 (P : Prop) :
  P∨¬P := by
  have step1 : ¬P∨P := thm_323 P
  have step2 (P Q : Prop) : ((P∨Q)→(Q∨P)) := axiom3 P Q
  have step3 : (¬P∨P)→(P∨¬P) := step2 (¬P) P
  exact step3 step1

theorem thm_325 (P : Prop) :
  P → ¬¬P := by
  have step1 (P : Prop) : P∨¬P := thm_324 P
  have step2 : ¬P∨¬¬P := step1 (¬P)
  rw [←@def1 P] at step2
  exact step2

-- theorem my_syllogism (P Q R : Prop) :
--   (P→Q)∧(Q→R) → (P→R) := by
--   have step1 : (Q→R)→((¬P∨Q)→(¬P∨R)) := axiom4
--   rw [and_iff_not_or_not]


theorem my_or_assoc (P Q R : Prop) :
  P∨(Q∨R) → (P∨Q)∨R := by
  have step1 : (P∨(Q∨R))→((P∨(Q∨R))∨R) := axiom2 (P∨(Q∨R)) R
  -- have step2 : P∨()
  sorry

  -- have step1 (P Q : Prop) : P→(P∨Q) := axiom1 P Q
  -- have step2 (P Q R : Prop) : (Q→R)→((P∨Q)→(P∨R)) := axiom4 P Q R
  -- have step3 (P Q : Prop) : (P→(P∨Q))→(((P∨Q)∨P)→((P∨Q)∨(P∨Q))) := step2 (P∨Q) P (P∨Q)
  -- have step4 (P Q : Prop) : ((P∨Q)∨P)→((P∨Q)∨(P∨Q)) := by
  --   apply step3 step1 P Q

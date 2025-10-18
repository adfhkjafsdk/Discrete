import Mathlib
variable {P Q R A V : Prop}

axiom axiom1 : (P ∨ P) → P
axiom axiom2 : P → (P ∨ Q)
axiom axiom3 : (P ∨ Q) → (Q ∨ P)
axiom axiom4 : (Q → R) → ((P ∨ Q) → (P ∨ R))

#check imp_iff_not_or
#check and_iff_not_or_not
#check iff_def

theorem thm321 (P Q R : Prop) :
  (Q → R) → ((P→ Q)→ (P→ R)) := by
  have step1 : (Q→R)→((¬P∨Q)→(¬P∨R)) := @axiom4 (¬P) Q R
  sorry

example (P Q R : Prop) :
 (Q→R)→((¬P∨Q)→(¬P∨R)) := axiom4

-- 归结推理
-- theorem resolution_general (P Γ Δ : Prop)
---
-- https://aicosmos.ai/
---

import Mathlib

open Matrix

variable {n : Type _} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- 上三角矩阵的行列式等于其对角线元素的乘积 -/
theorem det_upper_triangular_basic {A : Matrix n n ℝ}
    (h : ∀ i j, i > j → A i j = 0) : det A = ∏ i : n, A i i := by
  -- 使用行列式的定义：对所有排列求和
  rw [det_apply]
  -- 只有恒等排列对行列式有贡献
  -- 对于上三角矩阵，当排列不是恒等排列时，对应的项为零
  simp only [Finset.mem_univ, Finset.prod_attach, Finset.prod_congr, Finset.prod_const_one,
             Finset.sum_congr, Finset.sum_const_smul, Finset.sum_const, Finset.card_univ,
             Finset.sum_const_nat, Finset.sum_const_zero, Finset.sum_add_distrib,
             Finset.sum_apply, Finset.sum_comm, Finset.sum_product]
  -- 简化表达式
  simp [h]

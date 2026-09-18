import CP.Kernel.EvenInverse
import CP.OddBridge

namespace CP.Kernel
open Matrix Polynomial Finset

/-- 已有升阶矩阵的实际多项式系数作用，含首尾端点。 -/
theorem liftQ_polynomial (q : ℕ) (p : ℚ[X]) (hp : p.natDegree < q) (i : Fin (q+1)) :
    (liftQ q *ᵥ fun j => p.coeff j.val) i = ((1+X)*p).coeff i.val := by
  cases q with
  | zero => omega
  | succ q =>
    induction i using Fin.cases with
    | zero =>
      have hcast (j : Fin (q+1)) : (0 : Fin (q+2)) = j.castSucc ↔ j = 0 := by
        simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_zero, eq_comm]
      have hs (j : Fin (q+1)) : (0 : Fin (q+2)) ≠ j.succ := by
        intro h; have := congrArg Fin.val h; simp at this
      simp [Matrix.mulVec, dotProduct, liftQ, add_mul, Finset.sum_add_distrib,
        Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, hcast, hs]
    | succ i =>
      induction i using Fin.lastCases with
      | last =>
        have hcast (j : Fin (q+1)) : Fin.last (q+1) ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
        have hs (j : Fin (q+1)) : Fin.last (q+1) = j.succ ↔ j = Fin.last q := by
          simp only [Fin.ext_iff, Fin.val_last, Fin.val_succ]
          omega
        have hc : p.coeff (q+1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hp
        simp [Matrix.mulVec, dotProduct, liftQ, add_mul, Finset.sum_add_distrib,
          Polynomial.coeff_add, Polynomial.coeff_X_mul, hc, hcast, hs]
      | cast i =>
        have he : i.castSucc.succ = i.succ.castSucc := Fin.succ_castSucc i
        simp only [Matrix.mulVec, dotProduct, liftQ, add_mul, ite_mul, one_mul, zero_mul,
          Finset.sum_add_distrib]
        rw [he]
        simp only [Fin.castSucc_inj]
        rw [← he]
        simp only [Fin.succ_inj]
        simp [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul]

noncomputable def binomialVector (q k : ℕ) : Fin q → ℚ := fun i => (k.choose i.val : ℚ)

theorem liftQ_binomial (q k : ℕ) (hk : k < q) :
    liftQ q *ᵥ binomialVector q k = binomialVector (q+1) (k+1) := by
  funext i
  have hp : ((1+X : ℚ[X])^k).natDegree < q := by
    have hd : ((1+X : ℚ[X])^k).natDegree ≤ k := by compute_degree <;> norm_num
    omega
  have he := liftQ_polynomial q ((1+X)^k) hp i
  simp only [Polynomial.coeff_one_add_X_pow] at he
  rw [← pow_succ'] at he
  simpa only [Polynomial.coeff_one_add_X_pow, binomialVector] using he

/-- G^{-1} 的有限 Gram 和，复用已有条目公式。 -/
theorem G_inverse_gram_sum (q : ℕ) :
    (G q)⁻¹ = ∑ k : Fin q, Matrix.vecMulVec (binomialVector q k.val) (binomialVector q k.val) := by
  ext i j
  simp only [G_inverse_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, binomialVector]

/-- 升阶中的唯一边界项是 e₀e₀ᵀ，未截去任何无限矩阵边界。 -/
theorem G_inverse_lift_update (q : ℕ) :
    (G (q+1))⁻¹ = liftQ q*(G q)⁻¹*(liftQ q)ᵀ +
      Matrix.vecMulVec (Pi.single (0 : Fin (q+1)) 1) (Pi.single (0 : Fin (q+1)) 1) := by
  rw [G_inverse_gram_sum, G_inverse_gram_sum]
  rw [Fin.sum_univ_succ]
  have hzero : binomialVector (q+1) 0 = Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0
    · subst i; simp [binomialVector]
    · have hi' : 0 < i.val := by
        have : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
        omega
      simp [binomialVector, Nat.choose_eq_zero_of_lt hi', Pi.single_eq_of_ne hi]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [hzero]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [add_comm (Matrix.vecMulVec (Pi.single (0 : Fin (q+1)) (1:ℚ)) (Pi.single 0 1))]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply]
  have he := liftQ_binomial q k.val k.isLt
  have hei := congrFun he i
  have hej := congrFun he j
  simp only [Matrix.mulVec, dotProduct] at hei hej
  rw [← hei, ← hej]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end CP.Kernel

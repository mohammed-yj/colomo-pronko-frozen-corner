import CP.Kernel.Odd.Upgrade
import CP.Kernel.Odd.NullVector

namespace CP.Kernel
open Matrix Finset

theorem G_symmetric (q : ℕ) : (G q)ᵀ = G q := by
  rw [← B_gram, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem omega_skew (q : ℕ) : (omega q)ᵀ = -omega q := by
  simp only [omega, Matrix.transpose_sub, Matrix.transpose_mul, G_symmetric, R_transpose]
  abel

theorem jMatrix_skew (q : ℕ) : (jMatrix q)ᵀ = -jMatrix q := by
  simp only [jMatrix, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    G_symmetric, R_transpose]
  abel

theorem gammaOdd_skew {N : ℕ} (hN : 1 ≤ N) : (gammaOdd N)ᵀ = -gammaOdd N := by
  have he : ((omega (2*N))⁻¹)ᵀ = -(omega (2*N))⁻¹ := by
    rw [omega_inverse_eq_J_sub_C N hN, Matrix.transpose_sub, jMatrix_skew, cMatrix_skew hN]
    abel
  rw [gammaOdd_eq_lift_inverse hN, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, he]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem nu_left_omega_zero (N : ℕ) : nu N ᵥ* omega (2*N+1) = 0 := by
  rw [← Matrix.mulVec_transpose, omega_skew, Matrix.neg_mulVec, omega_nu_zero, neg_zero]

/-- Qᵀ 的一维核，由所有相邻坐标递推证明。 -/
theorem liftQ_transpose_kernel (q : ℕ) (v : Fin (q+1) → ℚ)
    (hv : (liftQ q)ᵀ *ᵥ v = 0) :
    v = fun i => alternating (q+1) i*v 0 := by
  have hs (j : Fin q) : v j.castSucc+v j.succ = 0 := by
    have he := congrFun hv j
    simpa [Matrix.mulVec, dotProduct, liftQ, Matrix.transpose_apply,
      add_mul, Finset.sum_add_distrib] using he
  funext i
  induction i using Fin.induction with
  | zero => simp [alternating]
  | succ i ih =>
    simp only [alternating, Fin.coe_castSucc, Fin.val_succ, pow_succ] at ih ⊢
    linear_combination hs i - ih

/-- (7.6) 的实际秩一缺陷；未假定奇数 Ω 可逆。 -/
theorem omega_gammaOdd {N : ℕ} (hN : 1 ≤ N) :
    omega (2*N+1)*gammaOdd N = 1-Matrix.vecMulVec
      (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N)) (nu N) := by
  let M := 1-omega (2*N+1)*gammaOdd N
  let a : Fin (2*N+1) → ℚ := fun j => M 0 j
  have hQ : (liftQ (2*N))ᵀ*M = 0 := by
    dsimp only [M]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, lift_omega_gammaOdd hN, sub_self]
  have hM : M = Matrix.vecMulVec (alternating (2*N+1)) a := by
    ext i j
    have hv : (liftQ (2*N))ᵀ *ᵥ (fun k => M k j) = 0 := by
      funext k
      exact congrFun (congrFun hQ k) j
    exact congrFun (liftQ_transpose_kernel (2*N) (fun k => M k j) hv) i
  have hνM : nu N ᵥ* M = nu N := by
    dsimp only [M]
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, ← Matrix.vecMul_vecMul,
      nu_left_omega_zero, Matrix.zero_vecMul, sub_zero]
  have hk : alternating (2*N+1) ⬝ᵥ nu N ≠ 0 := alternating_dot_nu_ne_zero N
  have ha (j : Fin (2*N+1)) :
      a j = nu N j/(alternating (2*N+1) ⬝ᵥ nu N) := by
    have he := congrFun hνM j
    rw [hM] at he
    simp only [Matrix.vecMul, dotProduct, Matrix.vecMulVec_apply] at he
    simp only [← mul_assoc] at he
    rw [← Finset.sum_mul] at he
    have hcomm : (∑ i, nu N i*alternating (2*N+1) i) = alternating (2*N+1) ⬝ᵥ nu N := by
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hcomm] at he
    apply (eq_div_iff hk).mpr
    simpa only [mul_comm] using he
  have hm : M = Matrix.vecMulVec
      (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N)) (nu N) := by
    rw [hM]
    ext i j
    simp only [Matrix.vecMulVec_apply, ha]
    ring
  rw [← hm]
  dsimp only [M]
  abel

theorem gammaOdd_omega {N : ℕ} (hN : 1 ≤ N) :
    gammaOdd N*omega (2*N+1) = 1-Matrix.vecMulVec (nu N)
      (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N)) := by
  have he := congrArg Matrix.transpose (omega_gammaOdd hN)
  simp only [Matrix.transpose_mul, omega_skew, gammaOdd_skew hN,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.transpose_sub, Matrix.transpose_one] at he
  have ht : (Matrix.vecMulVec
      (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N)) (nu N))ᵀ =
      Matrix.vecMulVec (nu N)
        (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N)) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
    ring
  rw [ht] at he
  exact he


noncomputable def centeredGammaOdd (N : ℕ) : Matrix (Fin (2*N+1)) (Fin (2*N+1)) ℚ :=
  centerProjection ⟨N, by omega⟩ (nu N)*gammaOdd N*(centerProjection ⟨N, by omega⟩ (nu N))ᵀ

/-- O3：先中心投影，再删中心，最后得到真正的逆矩阵。 -/
theorem odd_deleted_inverse {N : ℕ} (hN : 1 ≤ N) :
    (deleteCenter ⟨N, by omega⟩ (omega (2*N+1)))⁻¹ =
      deleteCenter ⟨N, by omega⟩ (centeredGammaOdd N) := by
  exact centered_deleted_inverse ⟨N, by omega⟩ (nu N)
    (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N))
    (nu_center_pos N).ne' (omega (2*N+1)) (gammaOdd N) (omega_nu_zero N) (omega_gammaOdd hN)

/-- 包含中心删除求和边界的显式右逆。 -/
theorem odd_deleted_mul_inverse {N : ℕ} (hN : 1 ≤ N) :
    deleteCenter ⟨N, by omega⟩ (omega (2*N+1))*
      deleteCenter ⟨N, by omega⟩ (centeredGammaOdd N) = 1 := by
  apply deleted_right_inverse ⟨N, by omega⟩ _ _ (fun i => nu N i/nu N ⟨N, by omega⟩)
  · exact projected_center_row _ _ (nu_center_pos N).ne' _
  · exact centered_product _ _ _ (nu_center_pos N).ne' _ _ (omega_nu_zero N) (omega_gammaOdd hN)

end CP.Kernel

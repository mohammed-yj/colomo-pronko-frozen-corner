import CP.Connection.OddGram

namespace CP.Connection
open Matrix CP.Kernel

theorem odd_baseL_det_ne_zero {N : ℕ} (hN : 1 ≤ N) : (baseL N (N+1)).det ≠ 0 := by
  have hs : (oddEliminated N).det ≠ 0 :=
    det_ne_zero_from_right_inverse _ _ (oddEliminated_right_inverse hN)
  have he := congrArg Matrix.det (odd_baseL_congruence N)
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose] at he
  have hl : (tailFirst (m:=N) (n:=N+1) (baseL N (N+1))).det = (baseL N (N+1)).det := by
    rw [tailFirst,Matrix.det_submatrix_equiv_self]
  rw [hl] at he
  intro hz
  rw [hz,mul_zero,zero_mul] at he
  exact hs he.symm

/-- 合同逆完整地回到候选坐标；此处尚未取任何主块。 -/
theorem odd_candidate_inverse {N : ℕ} (hN : 1 ≤ N) :
    (tailFirst (m:=N) (n:=N+1) (baseL N (N+1)))⁻¹ =
      (connectionB N (N+1))ᵀ*oddEliminatedInverse N*connectionB N (N+1) := by
  have hB : (connectionB N (N+1))⁻¹*connectionB N (N+1) = 1 :=
    Matrix.nonsing_inv_mul _ (connectionB_det_ne_zero N (N+1)).isUnit
  have hc := odd_baseL_congruence N
  change connectionB N (N+1)*tailFirst (m:=N) (n:=N+1) (baseL N (N+1))*(connectionB N (N+1))ᵀ = oddEliminated N at hc
  apply Matrix.inv_eq_right_inv
  calc
    _ = ((connectionB N (N+1))⁻¹*connectionB N (N+1))*tailFirst (m:=N) (n:=N+1) (baseL N (N+1))*
        (connectionB N (N+1))ᵀ*oddEliminatedInverse N*connectionB N (N+1) := by
      rw [hB,Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    _ = (connectionB N (N+1))⁻¹*(connectionB N (N+1)*tailFirst (m:=N) (n:=N+1) (baseL N (N+1))*
        (connectionB N (N+1))ᵀ)*oddEliminatedInverse N*connectionB N (N+1) := by
      simp only [Matrix.mul_assoc]
    _ = (connectionB N (N+1))⁻¹*(oddEliminated N*oddEliminatedInverse N)*connectionB N (N+1) := by
      rw [hc]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [oddEliminated_right_inverse hN,Matrix.mul_one,hB]

theorem odd_candidate_tail_formula {N : ℕ} (hN : 1 ≤ N) :
    LL (tailFirst (m:=N) (n:=N+1) ((baseL N (N+1))⁻¹)) =
      (B N)ᵀ*(oddX N)⁻¹*B N-
      (B N)ᵀ*oddE N*(H N (N+1))⁻¹*(oddZ N*(oddX N)⁻¹)*B N+
      (B N)ᵀ*oddE N*(H N (N+1))⁻¹*Y N (N+1)-
      (Y N (N+1))ᵀ*(H N (N+1))⁻¹*(oddZ N*(oddX N)⁻¹)*B N+
      (Y N (N+1))ᵀ*(H N (N+1))⁻¹*Y N (N+1) := by
  have hi : tailFirst (m:=N) (n:=N+1) ((baseL N (N+1))⁻¹) =
      (tailFirst (m:=N) (n:=N+1) (baseL N (N+1)))⁻¹ := by
    exact (Matrix.inv_submatrix_equiv _ (tailFirstEquiv N (N+1)) (tailFirstEquiv N (N+1))).symm
  rw [hi,odd_candidate_inverse hN,connectionB_blocks,blocks_transpose,
    oddEliminatedInverse,blocks_mul,blocks_mul,LL_blocks]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_add,Matrix.add_mul,
    Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_assoc]
  abel

/-- O4 的完整实际奇数连接式 (8.13)。 -/
theorem odd_connection {N : ℕ} (hN : 1 ≤ N) :
    1+LL (tailFirst (m:=N) (n:=N+1) ((baseL N (N+1))⁻¹)) =
      (U N)ᵀ*R N*trueOddS N*R N*U N := by
  have hs : (B N)ᵀ*trueOddS N*B N = (U N)ᵀ*R N*trueOddS N*R N*U N := by
    rw [B,Matrix.transpose_mul,R_transpose]
    simp only [Matrix.mul_assoc]
  rw [← hs,trueOddS_eq_free_add_inverse hN,Matrix.mul_add,Matrix.add_mul,
    freeOddS_congruence,odd_candidate_tail_formula hN,oddZ_mul_inverse hN]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
  abel

/-- 撤回列置换后，尾块是原候选矩阵的 N+1,…,2N 坐标。 -/
theorem odd_connection_native {N : ℕ} (hN : 1 ≤ N) :
    1+((K (N+(N+1))-tailDiagonal (N+(N+1)) N)⁻¹).submatrix
      (fun i : Fin N => (⟨N+1+i.val,by have := i.isLt; omega⟩ : Fin (N+(N+1))))
      (fun i : Fin N => (⟨N+1+i.val,by have := i.isLt; omega⟩ : Fin (N+(N+1)))) =
      (U N)ᵀ*R N*trueOddS N*R N*U N := by
  have ht (i : Fin N) : tailFirstEquiv N (N+1) (Fin.castAdd (N+1) i) =
      (⟨N+1+i.val,by have := i.isLt; omega⟩ : Fin (N+(N+1))) := by
    apply Fin.ext
    exact tailFirstEquiv_left_val N (N+1) i
  simpa only [baseL,LL,tailFirst,Matrix.submatrix_submatrix,Function.comp_def,ht] using odd_connection hN

end CP.Connection

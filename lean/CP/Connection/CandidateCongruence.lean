import CP.Connection.EvenFold

namespace CP.Connection
open Matrix

def baseL (m n : ℕ) : Matrix (Fin (m+n)) (Fin (m+n)) ℚ := K (m+n)-tailDiagonal (m+n) m

theorem connection_congruence (m n : ℕ) (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :
    connectionB m n*tailFirst (m:=m) (n:=n) A*(connectionB m n)ᵀ =
      paired (m:=m) (n:=n) (B (m+n)*A*(B (m+n))ᵀ) := by
  rw [connectionB,tailFirst,Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

theorem head_diagonal_after_tailFirst (m n : ℕ) :
    tailFirst (m:=m) (n:=n) (1-tailDiagonal (m+n) m) =
      blocks (0 : Matrix (Fin m) (Fin m) ℚ) 0 0 (1 : Matrix (Fin n) (Fin n) ℚ) := by
  ext i j
  have heq : tailFirstEquiv m n i = tailFirstEquiv m n j ↔ i = j := (tailFirstEquiv m n).injective.eq_iff
  simp only [tailFirst,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.one_apply,heq,
    tailDiagonal,Matrix.diagonal_apply,show m+n-m = n by omega]
  induction i using Fin.addCases <;> induction j using Fin.addCases
  all_goals simp only [tailFirstEquiv_left_val,tailFirstEquiv_right_val,
    blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply,Matrix.one_apply]
  · rename_i i j
    simp only [show n ≤ n+i.val by omega,if_true,sub_self]
  · rename_i i j
    simp only [show n ≤ n+i.val by omega,if_true,sub_self]
  · rename_i i j
    have hnj : ¬n ≤ i.val := by have := i.isLt; omega
    have hij : Fin.natAdd m i ≠ Fin.castAdd n j := by
      intro h; have := congrArg Fin.val h
      simp only [Fin.coe_natAdd,Fin.coe_castAdd] at this
      have := j.isLt
      omega
    simp [hnj,hij,-Fin.natAdd_eq_addNat]
  · rename_i i j
    have hni : ¬n ≤ i.val := by have := i.isLt; omega
    simp [hni,Fin.natAdd_inj,-Fin.natAdd_eq_addNat]

theorem head_diagonal_congruence (m n : ℕ) :
    paired (m:=m) (n:=n) (B (m+n)*(1-tailDiagonal (m+n) m)*(B (m+n))ᵀ) =
      blocks (0 : Matrix (Fin m) (Fin m) ℚ) 0 0 (H m n) := by
  rw [← connection_congruence,head_diagonal_after_tailFirst,connectionB_blocks,
    blocks_transpose,blocks_mul,blocks_mul]
  simp only [Matrix.zero_mul,Matrix.mul_zero,Matrix.one_mul,Matrix.mul_one,
    Matrix.transpose_zero,zero_add,add_zero,H]

/-- 实际候选矩阵的有限合同，保留所加回的整个前部对角。 -/
theorem baseL_congruence (m n : ℕ) :
    connectionB m n*tailFirst (m:=m) (n:=n) (baseL m n)*(connectionB m n)ᵀ =
      (paired (m:=m) (n:=n) (R (m+n))+1)*paired (G (m+n))*(paired (R (m+n))-1)+
        blocks (0 : Matrix (Fin m) (Fin m) ℚ) 0 0 (H m n) := by
  rw [connection_congruence]
  have hl : baseL m n = (K (m+n)-1)+(1-tailDiagonal (m+n) m) := by unfold baseL; abel
  rw [hl,Matrix.mul_add,Matrix.add_mul,paired_add,K_congruence,
    paired_mul,paired_mul,paired_add,paired_sub,paired_one,head_diagonal_congruence]

theorem blocks_add {m n : ℕ}
    (A A' : Matrix (Fin m) (Fin m) ℚ) (B B' : Matrix (Fin m) (Fin n) ℚ)
    (C C' : Matrix (Fin n) (Fin m) ℚ) (D D' : Matrix (Fin n) (Fin n) ℚ) :
    blocks A B C D+blocks A' B' C' D' = blocks (A+A') (B+B') (C+C') (D+D') := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [blocks,-Fin.natAdd_eq_addNat]

theorem blocks_sub {m n : ℕ}
    (A A' : Matrix (Fin m) (Fin m) ℚ) (B B' : Matrix (Fin m) (Fin n) ℚ)
    (C C' : Matrix (Fin n) (Fin m) ℚ) (D D' : Matrix (Fin n) (Fin n) ℚ) :
    blocks A B C D-blocks A' B' C' D' = blocks (A-A') (B-B') (C-C') (D-D') := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [blocks,-Fin.natAdd_eq_addNat]

/-- (8.1) 的实际候选矩阵合同。列置换将在逆矩阵尾块识别时撤回。 -/
theorem even_baseL_congruence (N : ℕ) :
    connectionB N N*tailFirst (m:=N) (n:=N) (baseL N N)*(connectionB N N)ᵀ =
      blocks (evenX N) (-evenX N) (evenX N) (H N N-evenX N) := by
  rw [baseL_congruence,paired_R_even]
  have hp : blocks (m:=N) (n:=N) (0 : Matrix (Fin N) (Fin N) ℚ) 1 1 0+1 = blocks (m:=N) (n:=N) 1 1 1 1 := by
    rw [← blocks_one N N,blocks_add]
    simp only [zero_add,add_zero]
  have hm : blocks (m:=N) (n:=N) (0 : Matrix (Fin N) (Fin N) ℚ) 1 1 0-1 = blocks (m:=N) (n:=N) (-1) 1 1 (-1) := by
    rw [← blocks_one N N,blocks_sub]
    simp only [zero_sub,sub_zero]
  rw [hp,hm]
  conv_lhs => rw [← blocks_reconstruct (paired (m:=N) (n:=N) (G (N+N)))]
  rw [blocks_mul,blocks_mul,blocks_add]
  simp only [Matrix.one_mul,Matrix.mul_one,Matrix.mul_neg,Matrix.neg_mul,zero_add,add_zero]
  congr 1 <;> unfold evenX <;> abel

end CP.Connection

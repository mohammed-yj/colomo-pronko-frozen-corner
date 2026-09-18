import CP.Connection.OddNormalization

namespace CP.Connection
open Matrix CP.Kernel Finset

@[simp] theorem mul_oddE_transpose_apply {N r : ℕ} (A : Matrix (Fin r) (Fin (N+1)) ℚ) (i : Fin r) (j : Fin N) :
    (A*(oddE N)ᵀ) i j = A i j.castSucc := by simp [oddE,Matrix.mul_apply,Matrix.transpose_apply]

@[simp] theorem mul_oddCorrection_apply {N r : ℕ} (A : Matrix (Fin r) (Fin (N+1)) ℚ) (i : Fin r) (j : Fin N) :
    (A*oddCorrection N) i j = A i (Fin.last N)*(2*nu N (oddLeft N j)/nu N (oddCenter N)) := by
  simp [oddCorrection,Matrix.mul_apply]

theorem inverseGram_odd_entry (N : ℕ) (i j : Fin (N+(N+1))) :
    inverseGram N (N+1) i j = (G (2*N+1))⁻¹ (oddPairEquiv N i) (oddPairEquiv N j) := by
  have hg : paired (m:=N) (n:=N+1) (G (N+(N+1))) =
      (G (2*N+1)).submatrix (oddPairEquiv N) (oddPairEquiv N) := by ext i j; rfl
  unfold inverseGram
  rw [hg,Matrix.inv_submatrix_equiv]
  rfl

theorem freeOddS_entry (N : ℕ) (i j : Fin N) :
    freeOddS N i j = -jMatrix (2*N+1) (oddLeft N i) (oddLeft N j)-
      jMatrix (2*N+1) (oddLeft N i) (oddLeft N j).rev+
      2/nu N (oddCenter N)*jMatrix (2*N+1) (oddLeft N i) (oddCenter N)*nu N (oddLeft N j) := by
  have hg (i j : Fin (2*N+1)) : jMatrix (2*N+1) i.rev j.rev = -jMatrix (2*N+1) i j := by
    have he := congrFun (congrFun (jMatrix_reflection (2*N+1)) i) j
    simpa only [mul_R_apply,R_mul_apply,Matrix.neg_apply] using he
  have hcc : jMatrix (2*N+1) (oddCenter N) (oddCenter N) = 0 := by
    have he := hg (oddCenter N) (oddCenter N)
    rw [oddCenter_rev] at he
    linarith
  have hcj := hg (oddCenter N) (oddLeft N j)
  rw [oddCenter_rev] at hcj
  unfold freeOddS
  rw [projected_entry _ _ _ hcc,projected_entry _ _ _ hcc,hcj,nu_rev_apply]
  ring

/-- (8.12) 的未作 V 合同版本，全部块均来自实际 G⁻¹。 -/
theorem freeOddS_inverseGram (N : ℕ) :
    freeOddS N = LL (inverseGram N (N+1))-oddE N*RR (inverseGram N (N+1))*(oddE N)ᵀ+
      LR (inverseGram N (N+1))*(oddE N)ᵀ-oddE N*RL (inverseGram N (N+1))+
      (oddE N*RR (inverseGram N (N+1))-LR (inverseGram N (N+1)))*oddCorrection N := by
  ext i j
  rw [freeOddS_entry]
  simp only [Matrix.add_apply,Matrix.sub_apply,mul_oddE_transpose_apply,oddE_mul_apply,
    mul_oddCorrection_apply,LL,LR,RL,RR,Matrix.submatrix_apply,inverseGram_odd_entry,
    oddPair_left,oddPair_right,oddPair_center,jMatrix,Matrix.sub_apply,R_mul_apply,mul_R_apply,Fin.rev_rev,oddCenter_rev]
  ring

/-- 自由核的 Gram 合同；使用既有四块 Gram 归一化。 -/
theorem freeOddS_congruence (N : ℕ) :
    (B N)ᵀ*freeOddS N*B N =
      1+(Y N (N+1))ᵀ*(H N (N+1))⁻¹*Y N (N+1)-
      (B N)ᵀ*oddE N*(H N (N+1))⁻¹*(oddE N)ᵀ*B N-
      (Y N (N+1))ᵀ*(H N (N+1))⁻¹*(oddE N)ᵀ*B N+
      (B N)ᵀ*oddE N*(H N (N+1))⁻¹*Y N (N+1)+
      ((B N)ᵀ*oddE N*(H N (N+1))⁻¹+(Y N (N+1))ᵀ*(H N (N+1))⁻¹)*oddCorrection N*B N := by
  rw [freeOddS_inverseGram]
  simp only [Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul]
  rw [inverseGram_LL_congruence,inverseGram_RR]
  have hLR := inverseGram_LR N (N+1)
  have hRL := inverseGram_RL N (N+1)
  simp only [Matrix.mul_assoc] at hLR hRL ⊢
  rw [← Matrix.mul_assoc (B N)ᵀ (LR (inverseGram N (N+1))),hLR,hRL]
  rw [← Matrix.mul_assoc (B N)ᵀ (LR (inverseGram N (N+1))),hLR]
  simp only [Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
  abel

end CP.Connection

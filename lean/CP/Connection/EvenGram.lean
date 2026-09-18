import CP.Connection.EvenElimination

namespace CP.Connection
open Matrix

@[simp] theorem LL_one (m n : ℕ) : LL (m:=m) (n:=n) 1 = 1 := by
  conv_lhs => rw [← blocks_one m n]
  rw [LL_blocks]
@[simp] theorem LR_one (m n : ℕ) : LR (m:=m) (n:=n) 1 = 0 := by
  conv_lhs => rw [← blocks_one m n]
  rw [LR_blocks]
@[simp] theorem RL_one (m n : ℕ) : RL (m:=m) (n:=n) 1 = 0 := by
  conv_lhs => rw [← blocks_one m n]
  rw [RL_blocks]
@[simp] theorem RR_one (m n : ℕ) : RR (m:=m) (n:=n) 1 = 1 := by
  conv_lhs => rw [← blocks_one m n]
  rw [RR_blocks]

theorem paired_inverse {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :
    paired (m:=m) (n:=n) A⁻¹ = (paired A)⁻¹ :=
  (Matrix.inv_submatrix_equiv A (pairedEquiv m n) (pairedEquiv m n)).symm

theorem gram_normalization (m n : ℕ) :
    (connectionB m n)ᵀ*(paired (m:=m) (n:=n) (G (m+n)))⁻¹*connectionB m n = 1 := by
  have hb : IsUnit (connectionB m n).det := (connectionB_det_ne_zero m n).isUnit
  have ht : IsUnit ((connectionB m n)ᵀ).det := by rw [Matrix.det_transpose]; exact hb
  rw [paired_G_gram,Matrix.mul_inv_rev]
  calc
    _ = ((connectionB m n)ᵀ*((connectionB m n)ᵀ)⁻¹)*((connectionB m n)⁻¹*connectionB m n) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ ht,Matrix.nonsing_inv_mul _ hb,Matrix.one_mul]

noncomputable def inverseGram (m n : ℕ) : Matrix (Fin (m+n)) (Fin (m+n)) ℚ :=
  (paired (m:=m) (n:=n) (G (m+n)))⁻¹

/-- Gram 合同的四个块，显式保留全部有限求和贡献。 -/
theorem gram_normalization_blocks (m n : ℕ) :
    blocks
      (((B m)ᵀ*LL (inverseGram m n)+(Y m n)ᵀ*RL (inverseGram m n))*B m+
        ((B m)ᵀ*LR (inverseGram m n)+(Y m n)ᵀ*RR (inverseGram m n))*Y m n)
      (((B m)ᵀ*LR (inverseGram m n)+(Y m n)ᵀ*RR (inverseGram m n))*H0 m n)
      (((H0 m n)ᵀ*RL (inverseGram m n))*B m+((H0 m n)ᵀ*RR (inverseGram m n))*Y m n)
      (((H0 m n)ᵀ*RR (inverseGram m n))*H0 m n) = 1 := by
  have he := gram_normalization m n
  change (connectionB m n)ᵀ*inverseGram m n*connectionB m n = 1 at he
  rw [connectionB_blocks,blocks_transpose] at he
  conv_lhs at he => rw [← blocks_reconstruct (inverseGram m n)]
  rw [blocks_mul,blocks_mul] at he
  simpa only [Matrix.transpose_zero,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero] using he

theorem inverseGram_RR (m n : ℕ) : RR (inverseGram m n) = (H m n)⁻¹ := by
  have he := congrArg (RR (m:=m) (n:=n)) (gram_normalization_blocks m n)
  rw [RR_blocks,RR_one] at he
  have h0 : H0 m n*(H0 m n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_H0]; exact isUnit_one)
  have hh : H m n*RR (inverseGram m n) = 1 := by
    calc
      _ = H0 m n*(((H0 m n)ᵀ*RR (inverseGram m n))*H0 m n)*(H0 m n)⁻¹ := by
        unfold H
        simp only [Matrix.mul_assoc]
        rw [h0,Matrix.mul_one]
      _ = 1 := by rw [he,Matrix.mul_one,h0]
  exact (Matrix.inv_eq_right_inv hh).symm

theorem inverseGram_LR (m n : ℕ) :
    (B m)ᵀ*LR (inverseGram m n) = -(Y m n)ᵀ*(H m n)⁻¹ := by
  have he := congrArg (LR (m:=m) (n:=n)) (gram_normalization_blocks m n)
  rw [LR_blocks,LR_one,inverseGram_RR] at he
  have h0 : H0 m n*(H0 m n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_H0]; exact isUnit_one)
  have hh := congrArg (fun A => A*(H0 m n)⁻¹) he
  dsimp only at hh
  rw [Matrix.mul_assoc,h0,Matrix.mul_one,Matrix.zero_mul] at hh
  rw [Matrix.neg_mul]
  exact eq_neg_of_add_eq_zero_left hh

theorem inverseGram_RL (m n : ℕ) :
    RL (inverseGram m n)*B m = -(H m n)⁻¹*Y m n := by
  have he := congrArg (RL (m:=m) (n:=n)) (gram_normalization_blocks m n)
  rw [RL_blocks,RL_one,inverseGram_RR] at he
  have h0 : ((H0 m n)ᵀ)⁻¹*(H0 m n)ᵀ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose,det_H0]; exact isUnit_one)
  have hh := congrArg (fun A => ((H0 m n)ᵀ)⁻¹*A) he
  dsimp only at hh
  rw [Matrix.mul_add] at hh
  simp only [← Matrix.mul_assoc,h0,Matrix.one_mul,Matrix.mul_zero] at hh
  rw [Matrix.neg_mul]
  exact eq_neg_of_add_eq_zero_left hh

theorem inverseGram_LL_congruence (m n : ℕ) :
    (B m)ᵀ*LL (inverseGram m n)*B m = 1+(Y m n)ᵀ*(H m n)⁻¹*Y m n := by
  have he := congrArg (LL (m:=m) (n:=n)) (gram_normalization_blocks m n)
  rw [LL_blocks,LL_one,inverseGram_RR] at he
  rw [Matrix.add_mul,Matrix.add_mul,Matrix.mul_assoc (Y m n)ᵀ, inverseGram_RL,
    inverseGram_LR] at he
  simp only [Matrix.mul_neg,Matrix.neg_mul,← Matrix.mul_assoc] at he
  have hh : (B m)ᵀ*LL (inverseGram m n)*B m-(Y m n)ᵀ*(H m n)⁻¹*Y m n = 1 := by
    convert he using 1 <;> abel
  calc
    _ = ((B m)ᵀ*LL (inverseGram m n)*B m-(Y m n)ᵀ*(H m n)⁻¹*Y m n)+
        (Y m n)ᵀ*(H m n)⁻¹*Y m n := by abel
    _ = _ := by rw [hh]

theorem freeD_inverseGram (N : ℕ) :
    freeD N = LL (inverseGram N N)-RR (inverseGram N N)+
      LR (inverseGram N N)-RL (inverseGram N N) := by
  unfold freeD jMatrix
  rw [paired_sub,paired_mul,paired_mul,paired_R_even,paired_inverse]
  change -LL (blocks (m:=N) (n:=N) 0 1 1 0*inverseGram N N-
    inverseGram N N*blocks (m:=N) (n:=N) 0 1 1 0)-LR
    (blocks (m:=N) (n:=N) 0 1 1 0*inverseGram N N-inverseGram N N*blocks (m:=N) (n:=N) 0 1 1 0) = _
  conv_lhs => rw [← blocks_reconstruct (inverseGram N N)]
  simp only [blocks_mul,blocks_sub,Matrix.zero_mul,Matrix.mul_zero,Matrix.one_mul,Matrix.mul_one,
    add_zero,zero_add,LL_blocks,LR_blocks]
  abel

/-- (8.4) 的实际 Gram 折叠合同。 -/
theorem freeD_congruence (N : ℕ) :
    (B N)ᵀ*freeD N*B N = 1+(Y N N)ᵀ*(H N N)⁻¹*Y N N-(B N)ᵀ*(H N N)⁻¹*B N-
      (Y N N)ᵀ*(H N N)⁻¹*B N+(B N)ᵀ*(H N N)⁻¹*Y N N := by
  rw [freeD_inverseGram]
  simp only [Matrix.mul_sub,Matrix.mul_add,Matrix.sub_mul,Matrix.add_mul]
  rw [inverseGram_LL_congruence,inverseGram_RR,inverseGram_LR,
    Matrix.mul_assoc (B N)ᵀ (RL (inverseGram N N)),inverseGram_RL]
  simp only [Matrix.neg_mul,Matrix.mul_neg,← Matrix.mul_assoc]
  abel

/-- F6：完整实际偶数连接式；左侧前块对应原坐标尾块。 -/
theorem even_connection {N : ℕ} (hN : 1 ≤ N) :
    1+LL (tailFirst (m:=N) (n:=N) ((baseL N N)⁻¹)) =
      (U N)ᵀ*R N*trueD N*R N*U N := by
  have hd : (B N)ᵀ*trueD N*B N = (U N)ᵀ*R N*trueD N*R N*U N := by
    rw [B,Matrix.transpose_mul,R_transpose]
    simp only [Matrix.mul_assoc]
  rw [← hd,trueD_eq_freeD_add_inverse hN,Matrix.mul_add,Matrix.add_mul,
    freeD_congruence,even_candidate_tail_formula hN]
  abel

end CP.Connection

import CP.Connection.Coordinates

namespace CP.Connection
open Matrix Finset

/-- 同时施加纸面反射行序和尾部优先列序的实际二项式矩阵。 -/
def connectionB (m n : ℕ) : Matrix (Fin (m+n)) (Fin (m+n)) ℚ :=
  (B (m+n)).submatrix (pairedEquiv m n) (tailFirstEquiv m n)

def H0 (m n : ℕ) : Matrix (Fin n) (Fin n) ℚ := RR (connectionB m n)
def Y (m n : ℕ) : Matrix (Fin n) (Fin m) ℚ := RL (connectionB m n)
def H (m n : ℕ) : Matrix (Fin n) (Fin n) ℚ := H0 m n*(H0 m n)ᵀ

theorem B_entry (q : ℕ) (i j : Fin q) :
    B q i j = (-1)^(i.val+j.rev.val)*(i.val.choose j.rev.val:ℚ) := by
  rw [B_eq_signed_T_R]
  simp only [mul_R_apply, signDiagonal, Matrix.diagonal_mul, T, pow_add]
  ring

theorem connectionB_LL (m n : ℕ) : LL (connectionB m n) = B m := by
  ext i j
  simp only [LL, connectionB, Matrix.submatrix_apply, pairedEquiv_left]
  rw [B_entry, B_entry]
  have he : (tailFirstEquiv m n (Fin.castAdd n j)).rev.val = j.rev.val := by
    rw [Fin.val_rev, tailFirstEquiv_left_val, Fin.val_rev]
    have := j.isLt
    omega
  rw [he]
  rfl

theorem connectionB_LR (m n : ℕ) : LR (connectionB m n) = 0 := by
  ext i j
  simp only [LR, connectionB, Matrix.submatrix_apply, pairedEquiv_left, Matrix.zero_apply]
  rw [B_entry]
  have he : i.val < (tailFirstEquiv m n (Fin.natAdd m j)).rev.val := by
    rw [Fin.val_rev, tailFirstEquiv_right_val]
    have := i.isLt
    have := j.isLt
    omega
  simp only [Fin.coe_castAdd]
  rw [Nat.choose_eq_zero_of_lt he, Nat.cast_zero, mul_zero]

theorem H0_entry (m n : ℕ) (i j : Fin n) :
    H0 m n i j = (-1)^((m+n-1-i.val)+(m+n-1-j.val))*
      ((m+n-1-i.val).choose (m+n-1-j.val):ℚ) := by
  simp only [H0, RR, connectionB, Matrix.submatrix_apply, pairedEquiv_right]
  rw [B_entry]
  have hi : (Fin.natAdd m i.rev).val = m+n-1-i.val := by
    simp only [Fin.coe_natAdd, Fin.val_rev]
    have := i.isLt
    omega
  have hj : (tailFirstEquiv m n (Fin.natAdd m j)).rev.val = m+n-1-j.val := by
    rw [Fin.val_rev, tailFirstEquiv_right_val]
    omega
  rw [hi,hj]

theorem H0_below (m n : ℕ) (i j : Fin n) (hj : j < i) : H0 m n i j = 0 := by
  rw [H0_entry, Nat.choose_eq_zero_of_lt (by have := i.isLt; have := j.isLt; omega),
    Nat.cast_zero, mul_zero]

theorem H0_diagonal (m n : ℕ) (i : Fin n) : H0 m n i i = 1 := by
  rw [H0_entry, Nat.choose_self, Nat.cast_one, mul_one, ← two_mul, pow_mul]
  norm_num

theorem det_H0 (m n : ℕ) : (H0 m n).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [H0_diagonal]
  · exact H0_below m n

theorem det_H (m n : ℕ) : (H m n).det = 1 := by
  rw [H, Matrix.det_mul, Matrix.det_transpose, det_H0, one_mul]

theorem B_det_ne_zero (m : ℕ) : (B m).det ≠ 0 := by
  have he := congrArg Matrix.det (B_gram m)
  rw [Matrix.det_mul,Matrix.det_transpose,det_G] at he
  intro hz
  rw [hz,zero_mul] at he
  exact zero_ne_one he

/-- 实际块识别：纸面 [0 V; H0 Y] 在列置换后为 [V 0; Y H0]。 -/
theorem connectionB_blocks (m n : ℕ) :
    connectionB m n = blocks (B m) 0 (Y m n) (H0 m n) := by
  rw [← blocks_reconstruct (connectionB m n), connectionB_LL, connectionB_LR]
  rfl

theorem paired_G_gram (m n : ℕ) :
    paired (m:=m) (n:=n) (G (m+n)) = connectionB m n*(connectionB m n)ᵀ := by
  symm
  rw [connectionB, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, B_gram]
  rfl

theorem paired_G_blocks (m n : ℕ) :
    paired (m:=m) (n:=n) (G (m+n)) =
      blocks (B m*(B m)ᵀ) (B m*(Y m n)ᵀ) (Y m n*(B m)ᵀ)
        (Y m n*(Y m n)ᵀ+H m n) := by
  rw [paired_G_gram,connectionB_blocks,blocks_transpose,blocks_mul]
  simp only [Matrix.transpose_zero,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,H]

end CP.Connection

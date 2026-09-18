import CP.Connection.EvenGram

namespace CP.Connection
open Matrix CP.Kernel

theorem even_tailFirst_LL (N : ℕ) (A : Matrix (Fin (N+N)) (Fin (N+N)) ℚ) :
    LL (tailFirst (m:=N) (n:=N) A) = A.submatrix (Fin.natAdd N) (Fin.natAdd N) := by
  have he (i : Fin N) : tailFirstEquiv N N (Fin.castAdd N i) = Fin.natAdd N i := by
    apply Fin.ext
    rw [tailFirstEquiv_left_val]
    rfl
  ext i j
  simp only [LL,tailFirst,Matrix.submatrix_apply,he]

/-- 实际 D_N 与规范 (5.3) 的逐项对应。 -/
theorem trueD_apply (N : ℕ) (i j : Fin N) :
    trueD N i j = -((cKernel N).coeff i.val).coeff j.val-
      ((cKernel N).coeff i.val).coeff (2*N-1-j.val) := by
  simp only [trueD,Matrix.sub_apply,Matrix.neg_apply,LL,LR,paired,Matrix.submatrix_apply,
    pairedEquiv_left,paired_even_right,evenC,kernelMatrix,Fin.coe_castAdd]
  have hj : (Fin.castAdd N j).rev.val = 2*N-1-j.val := by
    rw [Fin.val_rev,Fin.coe_castAdd]
    omega
  rw [hj]

/-- F6 原坐标版本：前块置换已撤回，左侧为真正的原尾部主块。 -/
theorem even_connection_native (N : ℕ) (hN : 1 ≤ N) :
    1+((K (N+N)-tailDiagonal (N+N) N)⁻¹).submatrix (Fin.natAdd N) (Fin.natAdd N) =
      (U N)ᵀ*R N*trueD N*R N*U N := by
  simpa only [even_tailFirst_LL,baseL] using even_connection hN

end CP.Connection

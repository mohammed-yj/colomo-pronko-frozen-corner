import CP.Kernel.Odd.KernelLift

namespace CP.Kernel
open Matrix

theorem jMatrix_lift_update (q : ℕ) :
    jMatrix (q+1) = liftQ q*jMatrix q*(liftQ q)ᵀ+oddBoundary q := by
  have ht := congrArg Matrix.transpose (R_liftQ q)
  simp only [Matrix.transpose_mul, R_transpose] at ht
  have hb : R (q+1)*Matrix.vecMulVec (Pi.single (0 : Fin (q+1)) (1:ℚ)) (Pi.single 0 1)-
      Matrix.vecMulVec (Pi.single (0 : Fin (q+1)) (1:ℚ)) (Pi.single 0 1)*R (q+1) =
      oddBoundary q := by
    ext i j
    have hi : i.rev = 0 ↔ i = Fin.last q := by
      rw [← Fin.rev_last, Fin.rev_inj]
    have hj : j.rev = 0 ↔ j = Fin.last q := by
      rw [← Fin.rev_last, Fin.rev_inj]
    simp only [Matrix.sub_apply, R_mul_apply, mul_R_apply, Matrix.vecMulVec_apply,
      oddBoundary, Pi.single_apply, hi, hj]
  unfold jMatrix
  rw [G_inverse_lift_update, Matrix.mul_add, Matrix.add_mul]
  have h1 : R (q+1)*(liftQ q*(G q)⁻¹*(liftQ q)ᵀ) =
      liftQ q*(R q*(G q)⁻¹)*(liftQ q)ᵀ := by
    simp only [← Matrix.mul_assoc]
    rw [R_liftQ]
  have h2 : (liftQ q*(G q)⁻¹*(liftQ q)ᵀ)*R (q+1) =
      liftQ q*((G q)⁻¹*R q)*(liftQ q)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← ht]
  rw [h1,h2,Matrix.mul_sub,Matrix.sub_mul]
  rw [← hb]
  abel

/-- 规范的实际奇数广义逆核。 -/
noncomputable def gammaOdd (N : ℕ) : Matrix (Fin (2*N+1)) (Fin (2*N+1)) ℚ :=
  jMatrix (2*N+1)-oMatrix N

/-- (7.3)：实际奇数核与已经证明的偶数真逆连接。 -/
theorem gammaOdd_eq_lift_inverse {N : ℕ} (hN : 1 ≤ N) :
    gammaOdd N = liftQ (2*N)*(omega (2*N))⁻¹*(liftQ (2*N))ᵀ := by
  rw [gammaOdd, jMatrix_lift_update, oMatrix_lift hN,
    omega_inverse_eq_J_sub_C N hN, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem gammaOdd_alternating {N : ℕ} (hN : 1 ≤ N) :
    gammaOdd N *ᵥ alternating (2*N+1) = 0 := by
  rw [gammaOdd_eq_lift_inverse hN, ← Matrix.mulVec_mulVec,
    liftQ_transpose_alternating, Matrix.mulVec_zero]

theorem lift_omega_gammaOdd {N : ℕ} (hN : 1 ≤ N) :
    (liftQ (2*N))ᵀ*omega (2*N+1)*gammaOdd N = (liftQ (2*N))ᵀ := by
  have hu : IsUnit (omega (2*N)).det := (omega_det_ne_zero N hN).isUnit
  rw [gammaOdd_eq_lift_inverse hN]
  calc
    _ = (((liftQ (2*N))ᵀ*omega (2*N+1)*liftQ (2*N))*(omega (2*N))⁻¹)*(liftQ (2*N))ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [liftQ_omega, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

end CP.Kernel

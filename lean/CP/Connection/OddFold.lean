import CP.Connection.EvenNative

namespace CP.Connection
open Matrix CP.Kernel Finset

def oddLeft (N : ℕ) (i : Fin N) : Fin (2*N+1) := ⟨i.val, by have := i.isLt; omega⟩
def oddCenter (N : ℕ) : Fin (2*N+1) := ⟨N, by omega⟩

noncomputable def trueOddS (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun i j =>
  -oMatrix N (oddLeft N i) (oddLeft N j)-oMatrix N (oddLeft N i) (oddLeft N j).rev+
    2/nu N (oddCenter N)*oMatrix N (oddLeft N i) (oddCenter N)*nu N (oddLeft N j)

noncomputable def projectedOddKernel (N : ℕ) :=
  centerProjection (oddCenter N) (nu N)*oMatrix N*(centerProjection (oddCenter N) (nu N))ᵀ

theorem gammaOdd_reflection {N : ℕ} (hN : 1 ≤ N) :
    R (2*N+1)*gammaOdd N*R (2*N+1) = -gammaOdd N := by
  have ht := congrArg Matrix.transpose (R_liftQ (2*N))
  simp only [Matrix.transpose_mul,R_transpose] at ht
  have he : R (2*N)*(omega (2*N))⁻¹*R (2*N) = -(omega (2*N))⁻¹ := by
    rw [omega_inverse_eq_J_sub_C N hN]
    exact j_sub_c_reflection hN
  rw [gammaOdd_eq_lift_inverse hN]
  calc
    _ = (R (2*N+1)*liftQ (2*N))*(omega (2*N))⁻¹*((liftQ (2*N))ᵀ*R (2*N+1)) := by
      simp only [Matrix.mul_assoc]
    _ = liftQ (2*N)*(R (2*N)*(omega (2*N))⁻¹*R (2*N))*(liftQ (2*N))ᵀ := by
      rw [R_liftQ,ht]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [he]; simp only [Matrix.mul_neg,Matrix.neg_mul]

theorem oMatrix_reflection {N : ℕ} (hN : 1 ≤ N) :
    R (2*N+1)*oMatrix N*R (2*N+1) = -oMatrix N := by
  have ho : oMatrix N = jMatrix (2*N+1)-gammaOdd N := by unfold gammaOdd; abel
  rw [ho,Matrix.mul_sub,Matrix.sub_mul,jMatrix_reflection,gammaOdd_reflection hN]
  abel

theorem oMatrix_skew {N : ℕ} (hN : 1 ≤ N) : (oMatrix N)ᵀ = -oMatrix N := by
  have ho : oMatrix N = jMatrix (2*N+1)-gammaOdd N := by unfold gammaOdd; abel
  rw [ho,Matrix.transpose_sub,jMatrix_skew,gammaOdd_skew hN]
  abel

theorem oddCenter_rev (N : ℕ) : (oddCenter N).rev = oddCenter N := by
  apply Fin.ext
  simp only [oddCenter,Fin.val_rev]
  omega

theorem nu_rev_apply (N : ℕ) (i : Fin (2*N+1)) : nu N i.rev = nu N i := by
  have he := congrFun (nu_reversal N) i
  simpa [Matrix.mulVec,dotProduct,R] using he

theorem oMatrix_center_zero {N : ℕ} (hN : 1 ≤ N) :
    oMatrix N (oddCenter N) (oddCenter N) = 0 := by
  have he := congrFun (congrFun (oMatrix_skew hN) (oddCenter N)) (oddCenter N)
  change oMatrix N (oddCenter N) (oddCenter N) = -oMatrix N (oddCenter N) (oddCenter N) at he
  linarith

/-- 复用已有中心投影，给出实际非中心条目的完整两项修正。 -/
theorem projected_entry {q : ℕ} (c : Fin q) (v : Fin q → ℚ)
    (A : Matrix (Fin q) (Fin q) ℚ) (hcc : A c c = 0) (i j : Fin q) :
    (centerProjection c v*A*(centerProjection c v)ᵀ) i j =
      A i j-v i/v c*A c j-A i c*(v j/v c) := by
  have hl (i j : Fin q) : (centerProjection c v*A) i j = A i j-v i/v c*A c j := by
    rw [centerProjection,Matrix.sub_mul,Matrix.one_mul]
    simp [Matrix.sub_apply,Matrix.mul_apply,Matrix.vecMulVec_apply,Pi.single_apply]
  have hr (B : Matrix (Fin q) (Fin q) ℚ) :
      (B*(centerProjection c v)ᵀ) i j = B i j-B i c*(v j/v c) := by
    rw [centerProjection_transpose,Matrix.mul_sub,Matrix.mul_one]
    simp [Matrix.sub_apply,Matrix.mul_apply,Matrix.vecMulVec_apply,Pi.single_apply]
  rw [hr,hl,hl,hcc,mul_zero,sub_zero]

/-- (8.7) 中实际 O 核经中心投影后的折叠。 -/
theorem trueOddS_projected_fold {N : ℕ} (hN : 1 ≤ N) (i j : Fin N) :
    trueOddS N i j = -projectedOddKernel N (oddLeft N i) (oddLeft N j)-
      projectedOddKernel N (oddLeft N i) (oddLeft N j).rev := by
  have he := congrFun (congrFun (oMatrix_reflection hN) (oddCenter N)) (oddLeft N j)
  simp only [mul_R_apply,R_mul_apply,oddCenter_rev,Matrix.neg_apply] at he
  unfold trueOddS projectedOddKernel
  rw [projected_entry _ _ _ (oMatrix_center_zero hN),projected_entry _ _ _ (oMatrix_center_zero hN),
    he,nu_rev_apply]
  ring

end CP.Connection

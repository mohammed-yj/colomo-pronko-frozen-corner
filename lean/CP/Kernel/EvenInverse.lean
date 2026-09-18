import CP.Kernel.ExactTruncation
import CP.EvenBridge

namespace CP.Kernel
open Matrix

/-- 实际 J 的反序反变性。 -/
theorem jMatrix_reflection (q : ℕ) : R q*jMatrix q*R q = -jMatrix q := by
  unfold jMatrix
  rw [Matrix.mul_sub, Matrix.sub_mul]
  have h1 : R q*(R q*(G q)⁻¹)*R q = (G q)⁻¹*R q := by
    rw [← Matrix.mul_assoc, R_sq, Matrix.one_mul]
  have h2 : R q*((G q)⁻¹*R q)*R q = R q*(G q)⁻¹ := by
    simp only [Matrix.mul_assoc, R_sq, Matrix.mul_one]
  rw [h1,h2]
  abel

theorem j_sub_c_reflection {N : ℕ} (hN : 1 ≤ N) :
    R (2*N)*(jMatrix (2*N)-cMatrix N)*R (2*N) = -(jMatrix (2*N)-cMatrix N) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, jMatrix_reflection, cMatrix_reflection hN]
  abel

theorem G_jMatrix (q : ℕ) :
    G q*jMatrix q = G q*R q*(G q)⁻¹-R q := by
  have hu : IsUnit (G q).det := by rw [det_G]; exact isUnit_one
  unfold jMatrix
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- 具体下降式的所有假设来自实际 P、C 核，无额外数学假设。 -/
theorem cp_descent {N : ℕ} (hN : 1 ≤ N) :
    G (2*N)*(jMatrix (2*N)-cMatrix N)+
      R (2*N)*G (2*N)*(jMatrix (2*N)-cMatrix N)*R (2*N) = -R (2*N) := by
  have hg : G (2*N)*(jMatrix (2*N)-cMatrix N) = -R (2*N)-pMatrix N := by
    rw [Matrix.mul_sub, G_jMatrix, G_cMatrix hN]
    abel
  calc
    _ = -R (2*N)-pMatrix N+R (2*N)*(-R (2*N)-pMatrix N)*R (2*N) := by
      rw [Matrix.mul_assoc (R (2*N)) (G (2*N)), hg]
    _ = -R (2*N)-R (2*N)-(pMatrix N+R (2*N)*pMatrix N*R (2*N)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, R_sq, Matrix.neg_mul, Matrix.one_mul]
      abel
    _ = -R (2*N) := by rw [pMatrix_reflection hN]; abel

/-- F5 核心：任意 N≥1 的实际有限矩阵右逆公式。 -/
theorem omega_mul_J_sub_C (N : ℕ) (hN : 1 ≤ N) :
    omega (2*N)*(jMatrix (2*N)-cMatrix N) = 1 := by
  exact inverse_from_descent (G (2*N)) (R (2*N)) (jMatrix (2*N)-cMatrix N)
    (R_sq (2*N)) (j_sub_c_reflection hN) (cp_descent hN)

/-- 有限同阶矩阵的右逆自动为真正逆；未假定 Ω 可逆。 -/
theorem omega_inverse_eq_J_sub_C (N : ℕ) (hN : 1 ≤ N) :
    (omega (2*N))⁻¹ = jMatrix (2*N)-cMatrix N := by
  exact inverse_from_descent_eq (G (2*N)) (R (2*N)) (jMatrix (2*N)-cMatrix N)
    (R_sq (2*N)) (j_sub_c_reflection hN) (cp_descent hN)

theorem omega_det_ne_zero (N : ℕ) (hN : 1 ≤ N) : (omega (2*N)).det ≠ 0 := by
  exact det_ne_zero_from_right_inverse _ _ (omega_mul_J_sub_C N hN)

end CP.Kernel

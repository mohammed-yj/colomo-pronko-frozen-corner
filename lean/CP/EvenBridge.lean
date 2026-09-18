import CP.BinomialMatrices

/-! Algebraic descent used at the end of F5.
The kernel identity `G*C = P + G*R*G⁻¹` is not established in this module.
Accordingly these are explicit conditional linear-algebra lemmas, not the
manuscript's instantiated core inverse theorem. -/
namespace CP
open Matrix

noncomputable def omega (q : ℕ) : Matrix (Fin q) (Fin q) ℚ := G q * R q - R q * G q
noncomputable def jMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  R q * (G q)⁻¹ - (G q)⁻¹ * R q

/-- Anticommutation converts the descent relation to a genuine right inverse. -/
theorem inverse_from_descent {q : ℕ} (A S X : Matrix (Fin q) (Fin q) ℚ)
    (hS : S*S = 1) (hX : S*X*S = -X)
    (hd : A*X + S*A*X*S = -S) : (A*S-S*A)*X = 1 := by
  have hx : X*S = -(S*X) := by
    have h := congrArg (fun Y => S*Y) hX
    simp only [← Matrix.mul_assoc, hS, Matrix.one_mul, Matrix.mul_neg] at h
    exact h
  have hh := congrArg (fun Y => Y*S) hd
  have hs : (S*A*X*S)*S = S*A*X := by
    simp only [Matrix.mul_assoc, hS, Matrix.mul_one]
  dsimp only at hh
  rw [Matrix.add_mul, hs, Matrix.neg_mul, hS] at hh
  calc
    (A*S-S*A)*X = -(A*X*S+S*A*X) := by
      rw [Matrix.sub_mul]
      have hx' : A*X*S = -(A*S*X) := by
        rw [Matrix.mul_assoc, hx, Matrix.mul_neg, ← Matrix.mul_assoc]
      rw [hx']; noncomm_ring
    _ = 1 := by rw [hh]; simp

/-- Over a finite square matrix ring, a right inverse is the actual inverse. -/
theorem inverse_from_descent_eq {q : ℕ} (A S X : Matrix (Fin q) (Fin q) ℚ)
    (hS : S*S = 1) (hX : S*X*S = -X)
    (hd : A*X + S*A*X*S = -S) : (A*S-S*A)⁻¹ = X := by
  exact Matrix.inv_eq_right_inv (inverse_from_descent A S X hS hX hd)

/-- Determinant nonvanishing follows from the right inverse, rather than being assumed. -/
theorem det_ne_zero_from_right_inverse {q : ℕ}
    (A X : Matrix (Fin q) (Fin q) ℚ) (h : A*X = 1) : A.det ≠ 0 := by
  have hh := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hh
  exact fun hz => by rw [hz, zero_mul] at hh; exact zero_ne_one hh

end CP

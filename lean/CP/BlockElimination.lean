import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

namespace CP
open Matrix

/-- Blocks are immediately reindexed to Fin (m+n), using the explicit finite equivalence. -/
def blocks {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin m) (Fin n) ℚ) (C : Matrix (Fin n) (Fin m) ℚ)
    (D : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin (m+n)) (Fin (m+n)) ℚ :=
  (Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem blocks_mul {m n : ℕ}
    (A A' : Matrix (Fin m) (Fin m) ℚ)
    (B B' : Matrix (Fin m) (Fin n) ℚ)
    (C C' : Matrix (Fin n) (Fin m) ℚ)
    (D D' : Matrix (Fin n) (Fin n) ℚ) :
    blocks A B C D * blocks A' B' C' D' =
      blocks (A*A'+B*C') (A*B'+B*D') (C*A'+D*C') (C*B'+D*D') := by
  unfold blocks
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blocks_one (m n : ℕ) :
    blocks (1 : Matrix (Fin m) (Fin m) ℚ) 0 0 (1 : Matrix (Fin n) (Fin n) ℚ) = 1 := by
  simp [blocks, Matrix.fromBlocks_one]

/-- All four blocks of the odd/general elimination inverse are checked.
X and H may have different finite sizes. -/
theorem elimination_right_inverse {m n : ℕ}
    (X Xi : Matrix (Fin m) (Fin m) ℚ) (H Hi : Matrix (Fin n) (Fin n) ℚ)
    (E : Matrix (Fin m) (Fin n) ℚ) (Z : Matrix (Fin n) (Fin m) ℚ)
    (hX : X*Xi = 1) (hH : H*Hi = 1) :
    blocks X (-X*E) Z (H-Z*E) *
      blocks (Xi-E*Hi*Z*Xi) (E*Hi) (-Hi*Z*Xi) Hi = 1 := by
  rw [blocks_mul]
  have h11 : X*(Xi-E*Hi*Z*Xi) + (-X*E)*(-Hi*Z*Xi) = 1 := by
    simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    simp only [Matrix.mul_assoc] at *
    rw [hX]
    abel
  have h12 : X*(E*Hi) + (-X*E)*Hi = 0 := by
    simp [Matrix.mul_assoc]
  have h21 : Z*(Xi-E*Hi*Z*Xi) + (H-Z*E)*(-Hi*Z*Xi) = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have hh : H*(Hi*(Z*Xi)) = Z*Xi := by rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hh]
    abel
  have h22 : Z*(E*Hi) + (H-Z*E)*Hi = 1 := by
    rw [Matrix.sub_mul, hH]
    simp only [Matrix.mul_assoc]
    abel
  rw [h11, h12, h21, h22, blocks_one]

theorem elimination_inverse {m n : ℕ}
    (X Xi : Matrix (Fin m) (Fin m) ℚ) (H Hi : Matrix (Fin n) (Fin n) ℚ)
    (E : Matrix (Fin m) (Fin n) ℚ) (Z : Matrix (Fin n) (Fin m) ℚ)
    (hX : X*Xi = 1) (hH : H*Hi = 1) :
    (blocks X (-X*E) Z (H-Z*E))⁻¹ =
      blocks (Xi-E*Hi*Z*Xi) (E*Hi) (-Hi*Z*Xi) Hi := by
  exact Matrix.inv_eq_right_inv (elimination_right_inverse X Xi H Hi E Z hX hH)

/-- The even inverse is a specialization, with both square blocks checked. -/
theorem even_elimination_inverse {n : ℕ}
    (X Xi H Hi : Matrix (Fin n) (Fin n) ℚ)
    (hX : X*Xi = 1) (hH : H*Hi = 1) :
    (blocks X (-X) X (H-X))⁻¹ = blocks (Xi-Hi) Hi (-Hi) Hi := by
  have hh := elimination_inverse X Xi H Hi 1 X hX hH
  simpa [Matrix.mul_assoc, hX] using hh

end CP

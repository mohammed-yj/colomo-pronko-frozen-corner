import CP.EvenBridge
import Mathlib.Data.Matrix.Rank

namespace CP
open Matrix Finset

/-- The finite lift multiplying coefficient vectors by 1+x. -/
def liftQ (q : ℕ) : Matrix (Fin (q+1)) (Fin q) ℚ := fun i j =>
  (if i = j.castSucc then 1 else 0) + (if i = j.succ then 1 else 0)

def alternating (q : ℕ) : Fin q → ℚ := fun i => (-1)^i.val

/-- The alternating covector annihilates the lift, for every finite order. -/
theorem liftQ_transpose_alternating (q : ℕ) :
    (liftQ q)ᵀ *ᵥ alternating (q+1) = 0 := by
  funext j
  simp [Matrix.mulVec, dotProduct, liftQ, Matrix.transpose_apply,
    add_mul, Finset.sum_add_distrib, alternating, pow_succ]

/-- The four terms in the finite lift, including both boundary embeddings. -/
theorem liftQ_sandwich_apply {q : ℕ}
    (A : Matrix (Fin (q+1)) (Fin (q+1)) ℚ) (i j : Fin q) :
    ((liftQ q)ᵀ*A*liftQ q) i j =
      A i.castSucc j.castSucc + A i.succ j.castSucc +
      A i.castSucc j.succ + A i.succ j.succ := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, liftQ,
    add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- The actual binomial Gram matrix is preserved by finite升阶. -/
theorem liftQ_G (q : ℕ) : (liftQ q)ᵀ*G (q+1)*liftQ q = G q := by
  ext i j
  rw [liftQ_sandwich_apply]
  simp only [G, Fin.coe_castSucc, Fin.val_succ]
  simp only [← Nat.add_assoc]
  have hb : ((i.val+1+j.val+1).choose (i.val+1) : ℚ) =
      ((i.val+1+j.val).choose (i.val+1) : ℚ) +
      ((i.val+j.val+1).choose i.val : ℚ) := by
    have h := Nat.choose_succ_succ' (i.val+j.val+1) i.val
    exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h :
      (i.val+1+j.val+1).choose (i.val+1) =
      (i.val+1+j.val).choose (i.val+1) + (i.val+j.val+1).choose i.val)
  rw [hb]
  have h1 : i.val+1+j.val = (i.val+j.val)+1 := by omega
  rw [h1]
  simp only [pow_succ]
  ring

/-- A concrete left inverse for the lift, obtained from the finite Gram identity. -/
theorem liftQ_left_inverse (q : ℕ) :
    ((G q)⁻¹*(liftQ q)ᵀ*G (q+1))*liftQ q = 1 := by
  calc
    _ = (G q)⁻¹*((liftQ q)ᵀ*G (q+1)*liftQ q) := by simp only [Matrix.mul_assoc]
    _ = (G q)⁻¹*G q := by rw [liftQ_G]
    _ = 1 := by
      apply Matrix.nonsing_inv_mul
      rw [det_G]
      exact isUnit_one

theorem liftQ_injective (q : ℕ) : Function.Injective (liftQ q).mulVec := by
  intro v w h
  have hh := congrArg (fun z => ((G q)⁻¹*(liftQ q)ᵀ*G (q+1))*ᵥz) h
  simpa only [Matrix.mulVec_mulVec, liftQ_left_inverse, Matrix.one_mulVec] using hh

/-- The lift has full column rank, with no restriction on q. -/
theorem rank_liftQ (q : ℕ) : (liftQ q).rank = q := by
  apply le_antisymm (Matrix.rank_le_width _)
  have h := Matrix.rank_mul_le_right ((G q)⁻¹*(liftQ q)ᵀ*G (q+1)) (liftQ q)
  simpa only [liftQ_left_inverse, Matrix.rank_one, Fintype.card_fin] using h

/-- Reversal commutes with the finite lift. -/
theorem R_liftQ (q : ℕ) : R (q+1)*liftQ q = liftQ q*R q := by
  ext i j
  rw [R_mul_apply, mul_R_apply]
  have h1 : i.rev = j.castSucc ↔ i = j.rev.succ := by
    constructor <;> intro h
    · simpa only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using congrArg Fin.rev h
    · simpa only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using congrArg Fin.rev h
  have h2 : i.rev = j.succ ↔ i = j.rev.castSucc := by
    constructor <;> intro h
    · simpa only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using congrArg Fin.rev h
    · simpa only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using congrArg Fin.rev h
  simp only [liftQ, h1, h2]
  ring

/-- The actual commutator Ω has the required finite lift compression. -/
theorem liftQ_omega (q : ℕ) :
    (liftQ q)ᵀ*omega (q+1)*liftQ q = omega q := by
  have ht := congrArg Matrix.transpose (R_liftQ q)
  simp only [Matrix.transpose_mul, R_transpose] at ht
  unfold omega
  rw [Matrix.mul_sub, Matrix.sub_mul]
  calc
    _ = ((liftQ q)ᵀ*G (q+1)*liftQ q)*R q -
        R q*((liftQ q)ᵀ*G (q+1)*liftQ q) := by
      congr 1
      · simp only [Matrix.mul_assoc]
        rw [R_liftQ]
      · simp only [← Matrix.mul_assoc]
        rw [ht]
    _ = _ := by rw [liftQ_G]

/-- Deleting a chosen coordinate uses the explicit finite embedding succAbove. -/
def deleteCenter {q : ℕ} (c : Fin (q+1))
    (A : Matrix (Fin (q+1)) (Fin (q+1)) ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  A.submatrix c.succAbove c.succAbove

/-- The missing center term is explicitly zero; no infinite truncation is used. -/
theorem delete_mul_of_zero_row {q : ℕ} (c : Fin (q+1))
    (A B : Matrix (Fin (q+1)) (Fin (q+1)) ℚ)
    (hB : ∀ j, B c j = 0) :
    deleteCenter c (A*B) = deleteCenter c A * deleteCenter c B := by
  ext i j
  change (∑ k : Fin (q+1), A (c.succAbove i) k * B k (c.succAbove j)) = _
  rw [Fin.sum_univ_succAbove _ c]
  simp [hB, deleteCenter, Matrix.mul_apply, Matrix.submatrix_apply]

/-- Correct center-deletion inverse theorem. A projected full inverse is used,
not a principal block of the inverse of the original matrix. -/
theorem deleted_right_inverse {q : ℕ} (c : Fin (q+1))
    (A B : Matrix (Fin (q+1)) (Fin (q+1)) ℚ) (v : Fin (q+1) → ℚ)
    (hB : ∀ j, B c j = 0)
    (hAB : A*B = 1 - Matrix.vecMulVec (Pi.single c 1) v) :
    deleteCenter c A * deleteCenter c B = 1 := by
  rw [← delete_mul_of_zero_row c A B hB, hAB]
  ext i j
  have hi : c.succAbove i ≠ c := Fin.succAbove_ne c i
  simp [deleteCenter, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, hi,
    Fin.succAbove_right_injective.eq_iff]

/-- The deleted projected matrix is the actual inverse in its finite matrix ring. -/
theorem deleted_inverse {q : ℕ} (c : Fin (q+1))
    (A B : Matrix (Fin (q+1)) (Fin (q+1)) ℚ) (v : Fin (q+1) → ℚ)
    (hB : ∀ j, B c j = 0)
    (hAB : A*B = 1 - Matrix.vecMulVec (Pi.single c 1) v) :
    (deleteCenter c A)⁻¹ = deleteCenter c B := by
  exact Matrix.inv_eq_right_inv (deleted_right_inverse c A B v hB hAB)

/-- The center projection in the manuscript, with its pivot explicitly supplied. -/
def centerProjection {q : ℕ} (c : Fin q) (v : Fin q → ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  1 - Matrix.vecMulVec (fun i => v i / v c) (Pi.single c 1)

theorem centerProjection_row {q : ℕ} (c : Fin q) (v : Fin q → ℚ)
    (hc : v c ≠ 0) (j : Fin q) : centerProjection c v c j = 0 := by
  simp [centerProjection, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, hc, Pi.single_apply, eq_comm]

/-- Both center rows and columns vanish after the congruence. -/
theorem projected_center_row {q : ℕ} (c : Fin q) (v : Fin q → ℚ)
    (hc : v c ≠ 0) (Γ : Matrix (Fin q) (Fin q) ℚ) (j : Fin q) :
    (centerProjection c v * Γ * (centerProjection c v)ᵀ) c j = 0 := by
  simp [Matrix.mul_apply, centerProjection_row c v hc]


/-- Multiplication by a rank-one matrix, proved by a finite sum. -/
theorem mul_outer {q : ℕ} (A : Matrix (Fin q) (Fin q) ℚ) (u v : Fin q → ℚ) :
    A*Matrix.vecMulVec u v = Matrix.vecMulVec (A*ᵥu) v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    ← mul_assoc, Finset.sum_mul]

theorem centerProjection_mulVec {q : ℕ} (c : Fin q) (v : Fin q → ℚ)
    (hc : v c ≠ 0) : centerProjection c v *ᵥv = 0 := by
  rw [centerProjection, Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Pi.single_apply, mul_assoc, hc]

theorem mul_centerProjection {q : ℕ} (c : Fin q) (v : Fin q → ℚ)
    (A : Matrix (Fin q) (Fin q) ℚ) (hAv : A*ᵥv = 0) :
    A*centerProjection c v = A := by
  have hv : A*ᵥ(fun i => v i/v c) = 0 := by
    funext i
    have hi := congrFun hAv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi ⊢
    simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
    rw [hi, zero_mul]
  rw [centerProjection, Matrix.mul_sub, Matrix.mul_one, mul_outer, hv]
  have hz : Matrix.vecMulVec (0 : Fin q → ℚ) (Pi.single c 1) = 0 := by
    ext i j; simp [Matrix.vecMulVec_apply]
  rw [hz, sub_zero]

theorem outer_mul_projection_transpose {q : ℕ} (c : Fin q)
    (v z : Fin q → ℚ) (hc : v c ≠ 0) :
    Matrix.vecMulVec z v*(centerProjection c v)ᵀ = 0 := by
  ext i j
  have hv := congrFun (centerProjection_mulVec c v hc) j
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hv
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply,
    Matrix.zero_apply]
  calc
    _ = z i * ∑ k, centerProjection c v j k * v k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = 0 := by rw [hv, mul_zero]

theorem centerProjection_transpose {q : ℕ} (c : Fin q) (v : Fin q → ℚ) :
    (centerProjection c v)ᵀ =
      1-Matrix.vecMulVec (Pi.single c 1) (fun i => v i/v c) := by
  rw [centerProjection, Matrix.transpose_sub, Matrix.transpose_one]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]

/-- Central projection computes the full product before any coordinate is removed.
The hypotheses describe the unprojected operator; the projected inverse formula
is proved here and is not included among the assumptions. -/
theorem centered_product {q : ℕ} (c : Fin q) (v z : Fin q → ℚ)
    (hc : v c ≠ 0) (A Γ : Matrix (Fin q) (Fin q) ℚ)
    (hAv : A*ᵥv = 0) (hAΓ : A*Γ = 1-Matrix.vecMulVec z v) :
    A*(centerProjection c v*Γ*(centerProjection c v)ᵀ) =
      1-Matrix.vecMulVec (Pi.single c 1) (fun i => v i/v c) := by
  calc
    _ = (A*centerProjection c v)*Γ*(centerProjection c v)ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = (1-Matrix.vecMulVec z v)*(centerProjection c v)ᵀ := by
      rw [mul_centerProjection c v A hAv, hAΓ]
    _ = (centerProjection c v)ᵀ := by
      rw [Matrix.sub_mul, Matrix.one_mul, outer_mul_projection_transpose c v z hc, sub_zero]
    _ = _ := centerProjection_transpose c v

/-- The complete finite center-deletion argument, conditional only on the
unprojected kernel and product identities. -/
theorem centered_deleted_inverse {q : ℕ} (c : Fin (q+1))
    (v z : Fin (q+1) → ℚ) (hc : v c ≠ 0)
    (A Γ : Matrix (Fin (q+1)) (Fin (q+1)) ℚ)
    (hAv : A*ᵥv = 0) (hAΓ : A*Γ = 1-Matrix.vecMulVec z v) :
    (deleteCenter c A)⁻¹ =
      deleteCenter c (centerProjection c v*Γ*(centerProjection c v)ᵀ) := by
  apply deleted_inverse c A _ (fun i => v i/v c)
  · exact projected_center_row c v hc Γ
  · exact centered_product c v z hc A Γ hAv hAΓ

end CP

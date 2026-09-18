import CP.BlockElimination
import CP.OddBridge

/-! Finite determinant identities used in normalization and diagonal add-back.
These theorems are not yet instantiated at the explicit true kernel. -/
namespace CP
open Matrix

/-- Rectangular update over Q. The matrix dimensions are arbitrary finite orders. -/
theorem det_update {q s : ℕ} (A : Matrix (Fin q) (Fin q) ℚ)
    (U : Matrix (Fin q) (Fin s) ℚ) (V : Matrix (Fin s) (Fin q) ℚ)
    (hA : A.det ≠ 0) :
    (A+U*V).det = A.det * (1+V*A⁻¹*U).det := by
  exact Matrix.det_add_mul U V (isUnit_iff_ne_zero.mpr hA)

/-- Explicit finite inclusion of the first m coordinates. -/
def frontEmbedding {q m : ℕ} (h : m ≤ q) : Fin m ↪ Fin q :=
  ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩, by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin q => x.val) hij⟩

/-- Selection matrix associated with a finite embedding. -/
def selection {q s : ℕ} (e : Fin s ↪ Fin q) : Matrix (Fin q) (Fin s) ℚ :=
  fun i j => if i = e j then 1 else 0

theorem selection_compress {q s : ℕ} (e : Fin s ↪ Fin q)
    (A : Matrix (Fin q) (Fin q) ℚ) :
    (selection e)ᵀ * A * selection e = A.submatrix e e := by
  ext i j
  simp [selection, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]

/-- Adding any selected set of diagonal entries is reduced to a genuine inverse block. -/
theorem det_diagonal_add_back {q s : ℕ} (e : Fin s ↪ Fin q)
    (A : Matrix (Fin q) (Fin q) ℚ) (hA : A.det ≠ 0) :
    (A+selection e*(selection e)ᵀ).det =
      A.det * (1+A⁻¹.submatrix e e).det := by
  rw [det_update A _ _ hA, selection_compress]


/-- Selection intertwines a finite matrix with its compressed action when
all omitted rows of the selected columns are zero. -/
theorem selection_intertwine {q s : ℕ} (e : Fin s ↪ Fin q)
    (U : Matrix (Fin q) (Fin q) ℚ)
    (hU : ∀ i, (∀ k, i ≠ e k) → ∀ j, U i (e j) = 0) :
    U*selection e = selection e*U.submatrix e e := by
  ext i j
  simp only [Matrix.mul_apply, selection, Matrix.submatrix_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k,rfl⟩ := hi
    simp [e.injective.eq_iff]
  · have hz : ∀ k, i ≠ e k := by simpa using hi
    simp [hz, hU i hz j]

/-- Exact principal congruence, with no interchange of inverse and submatrix. -/
theorem selected_congruence {q s : ℕ} (e : Fin s ↪ Fin q)
    (U D : Matrix (Fin q) (Fin q) ℚ)
    (hU : ∀ i, (∀ k, i ≠ e k) → ∀ j, U i (e j) = 0) :
    (Uᵀ*D*U).submatrix e e =
      (U.submatrix e e)ᵀ * D.submatrix e e * U.submatrix e e := by
  rw [← selection_compress]
  have h := selection_intertwine e U hU
  calc
    _ = (U*selection e)ᵀ*D*(U*selection e) := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (selection e*U.submatrix e e)ᵀ*D*(selection e*U.submatrix e e) := by rw [h]
    _ = (U.submatrix e e)ᵀ*((selection e)ᵀ*D*selection e)*U.submatrix e e := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [selection_compress]

/-- A front principal block of an upper-triangular matrix satisfies the
finite support condition needed above. -/
theorem front_upper_support {q m : ℕ} (h : m ≤ q)
    (U : Matrix (Fin q) (Fin q) ℚ)
    (hU : ∀ i j, j < i → U i j = 0) :
    ∀ i, (∀ k, i ≠ frontEmbedding h k) → ∀ j, U i (frontEmbedding h j) = 0 := by
  intro i hi j
  apply hU
  change j.val < i.val
  by_contra hij
  have him : i.val < m := lt_of_le_of_lt (by omega) j.isLt
  exact hi ⟨i.val, him⟩ (by apply Fin.ext; rfl)

/-- Unit upper-triangular front blocks have determinant one. -/
theorem det_front_unit_upper {q m : ℕ} (h : m ≤ q)
    (U : Matrix (Fin q) (Fin q) ℚ)
    (hU : ∀ i j, j < i → U i j = 0) (hdiag : ∀ i, U i i = 1) :
    (U.submatrix (frontEmbedding h) (frontEmbedding h)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [Matrix.submatrix_apply, hdiag]
  · intro i j hij
    exact hU _ _ hij

/-- The front principal determinant is unchanged by unit upper-triangular congruence. -/
theorem det_front_congruence {q m : ℕ} (h : m ≤ q)
    (U D : Matrix (Fin q) (Fin q) ℚ)
    (hU : ∀ i j, j < i → U i j = 0) (hdiag : ∀ i, U i i = 1) :
    ((Uᵀ*D*U).submatrix (frontEmbedding h) (frontEmbedding h)).det =
      (D.submatrix (frontEmbedding h) (frontEmbedding h)).det := by
  rw [selected_congruence _ U D (front_upper_support h U hU)]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_front_unit_upper h U hU hdiag]
  ring

end CP

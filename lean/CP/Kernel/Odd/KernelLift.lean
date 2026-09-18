import CP.Kernel.Odd.Lift

namespace CP.Kernel
open Polynomial Matrix Finset

/-- 有限二元多项式的实际系数矩阵。 -/
noncomputable def kernelMatrix (q : ℕ) (p : Bivariate) : Matrix (Fin q) (Fin q) ℚ :=
  fun i j => (p.coeff i.val).coeff j.val

theorem column_degree_lt {q : ℕ} (p : Bivariate) (hp : p.natDegree < q) (j : ℕ) :
    ((swapXY p).coeff j).natDegree < q := by
  have hb : ((swapXY p).coeff j).natDegree ≤ q-1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [swap_coeff]
    have hz : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, Polynomial.coeff_zero]
  omega


theorem swapXY_twice (p : Bivariate) : swapXY (swapXY p) = p := by
  ext i j
  simp only [swap_coeff]

theorem row_degree_lt {q : ℕ} (p : Bivariate) (hp : (swapXY p).natDegree < q) (i : ℕ) :
    (p.coeff i).natDegree < q := by
  simpa only [swapXY_twice] using column_degree_lt (swapXY p) hp i

theorem lifted_column (p : Bivariate) (j : ℕ) :
    (swapXY ((1+xx)*p)).coeff j = (1+X)*(swapXY p).coeff j := by
  rw [map_mul, map_add, map_one, swap_xx]
  change ((1+C X)*swapXY p).coeff j = _
  rw [← Polynomial.C_1, ← Polynomial.C_add, Polynomial.coeff_C_mul]

theorem liftQ_column {q : ℕ} (p : Bivariate) (hp : p.natDegree < q)
    (i : Fin (q+1)) (j : ℕ) :
    (∑ k : Fin q, liftQ q i k*(p.coeff k.val).coeff j) =
      (((1+xx)*p).coeff i.val).coeff j := by
  have he := liftQ_polynomial q ((swapXY p).coeff j) (column_degree_lt p hp j) i
  simp only [Matrix.mulVec, dotProduct, swap_coeff] at he
  rw [← lifted_column p j, swap_coeff] at he
  exact he

theorem kernelMatrix_lift {q : ℕ} (p : Bivariate)
    (hx : p.natDegree < q) (hy : (swapXY p).natDegree < q) :
    kernelMatrix (q+1) ((1+xx)*(1+yy)*p) = liftQ q*kernelMatrix q p*(liftQ q)ᵀ := by
  have hly : (swapXY ((1+xx)*p)).natDegree < q := by
    rw [map_mul, map_add, map_one, swap_xx]
    have hzero : (1+yy).natDegree = 0 := by
      change (1+C X : Bivariate).natDegree = 0
      rw [← Polynomial.C_1, ← Polynomial.C_add, Polynomial.natDegree_C]
    have he := Polynomial.natDegree_mul_le (p := 1+yy) (q := swapXY p)
    rw [hzero, zero_add] at he
    exact he.trans_lt hy
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, kernelMatrix, Matrix.transpose_apply]
  simp_rw [liftQ_column p hx i]
  have he := liftQ_polynomial q (((1+xx)*p).coeff i.val) (row_degree_lt _ hly _) j
  simp only [Matrix.mulVec, dotProduct] at he
  have hp : (1+xx)*(1+yy)*p = (1+yy)*((1+xx)*p) := by ring
  rw [hp]
  have hc : ((1+yy)*((1+xx)*p)).coeff i.val = (1+X)*(((1+xx)*p).coeff i.val) := by
    change ((1+C X)*((1+xx)*p)).coeff i.val = _
    rw [← Polynomial.C_1, ← Polynomial.C_add, Polynomial.coeff_C_mul]
  rw [hc, ← he]
  apply Finset.sum_congr rfl
  intro k hk
  ring

noncomputable def oddKernel (N : ℕ) : Bivariate :=
  (1+xx)*(1+yy)*cKernel N+xx^(2*N)-yy^(2*N)

/-- 规范 (4.15) 的实际 O^{(N)} 系数。 -/
noncomputable def oMatrix (N : ℕ) : Matrix (Fin (2*N+1)) (Fin (2*N+1)) ℚ :=
  kernelMatrix (2*N+1) (oddKernel N)

noncomputable def oddBoundary (q : ℕ) : Matrix (Fin (q+1)) (Fin (q+1)) ℚ :=
  Matrix.vecMulVec (Pi.single (Fin.last q) 1) (Pi.single 0 1) -
  Matrix.vecMulVec (Pi.single 0 1) (Pi.single (Fin.last q) 1)

theorem boundary_kernel_coeff (q : ℕ) : kernelMatrix (q+1) (xx^q-yy^q) = oddBoundary q := by
  ext i j
  have hm (a b : ℕ) : ((xx^a*yy^b).coeff i.val).coeff j.val =
      (if i.val = a then 1 else 0)*(if j.val = b then 1 else 0) := by
    simp only [xx, yy, ← Polynomial.C_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
    by_cases ha : i.val = a <;> simp [ha, eq_comm, Polynomial.coeff_X_pow]
  have hx := hm q 0
  have hy := hm 0 q
  simp only [pow_zero, mul_one, one_mul] at hx hy
  simp only [kernelMatrix, Polynomial.coeff_sub, oddBoundary, Matrix.sub_apply,
    Matrix.vecMulVec_apply]
  rw [hx, hy]
  have hi : i.val = q ↔ i = Fin.last q := by simp only [Fin.ext_iff, Fin.val_last]
  have hj : j.val = q ↔ j = Fin.last q := by simp only [Fin.ext_iff, Fin.val_last]
  have hi0 : i.val = 0 ↔ i = 0 := by simp only [Fin.ext_iff, Fin.val_zero]
  have hj0 : j.val = 0 ↔ j = 0 := by simp only [Fin.ext_iff, Fin.val_zero]
  simp only [Pi.single_apply, ← hi, ← hj, ← hi0, ← hj0]


theorem oMatrix_lift {N : ℕ} (hN : 1 ≤ N) :
    oMatrix N = liftQ (2*N)*cMatrix N*(liftQ (2*N))ᵀ+oddBoundary (2*N) := by
  have hx : (cKernel N).natDegree < 2*N := by have := cKernel_degree hN; omega
  have hy : (swapXY (cKernel N)).natDegree < 2*N := by have := swap_cKernel_degree hN; omega
  have he := kernelMatrix_lift (cKernel N) hx hy
  have hb := boundary_kernel_coeff (2*N)
  unfold oMatrix oddKernel
  ext i j
  have hp : (1+xx)*(1+yy)*cKernel N+xx^(2*N)-yy^(2*N) =
      (1+xx)*(1+yy)*cKernel N+(xx^(2*N)-yy^(2*N)) := by ring
  rw [hp]
  change ((_ + _ : Bivariate).coeff i.val).coeff j.val = _
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  exact congrFun (congrFun (congrArg₂ (·+·) he hb) i) j

end CP.Kernel

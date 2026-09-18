import CP.Kernel.Bidegree

namespace CP.Kernel
open Polynomial

/-- 两个变量交换后的逐项系数公式，没有无限矩阵截断。 -/
theorem swap_coeff (p : Bivariate) (i j : ℕ) :
    ((swapXY p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial n a =>
    simp only [swapXY, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      yy, ← Polynomial.C_pow, Polynomial.coeff_mul_C,
      Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_monomial]
    split_ifs <;> simp_all [eq_comm]

/-- 固定次数的双变量反射，通过两次有限单变量反射实现。 -/
noncomputable def reflectXY (d : ℕ) (p : Bivariate) : Bivariate :=
  swapXY ((swapXY (p.reflect d)).reflect d)

theorem reflectXY_coeff (d : ℕ) (p : Bivariate) (i j : ℕ) :
    ((reflectXY d p).coeff i).coeff j =
      (p.coeff (Polynomial.revAt d i)).coeff (Polynomial.revAt d j) := by
  simp only [reflectXY, swap_coeff, Polynomial.coeff_reflect]

theorem swap_reflect_degree (p : Bivariate) (d k : ℕ)
    (hp : (swapXY p).natDegree ≤ k) :
    (swapXY (p.reflect d)).natDegree ≤ k := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  ext j
  rw [swap_coeff, Polynomial.coeff_reflect, ← swap_coeff]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hi)]
  simp

theorem reflectXY_add (d : ℕ) (p q : Bivariate) :
    reflectXY d (p+q) = reflectXY d p + reflectXY d q := by
  simp only [reflectXY, Polynomial.reflect_add, map_add]

theorem reflectXY_sub (d : ℕ) (p q : Bivariate) :
    reflectXY d (p-q) = reflectXY d p - reflectXY d q := by
  ext i j
  simp only [reflectXY_coeff, Polynomial.coeff_sub]

theorem reflectXY_scalar (d : ℕ) (r : ℚ) (p : Bivariate) :
    reflectXY d (C (C r)*p) = C (C r)*reflectXY d p := by
  ext i j
  simp only [reflectXY_coeff, Polynomial.coeff_C_mul]

theorem reflectXY_separated (d : ℕ) (p q : ℚ[X]) :
    reflectXY d (inX p*inY q) = inX (p.reflect d)*inY (q.reflect d) := by
  ext i j
  simp only [reflectXY_coeff, inX, inY, Polynomial.coeff_mul_C,
    Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_reflect]

theorem reflectXY_mul (p q : Bivariate) (d e : ℕ)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ e)
    (hpy : (swapXY p).natDegree ≤ d) (hqy : (swapXY q).natDegree ≤ e) :
    reflectXY (d+e) (p*q) = reflectXY d p*reflectXY e q := by
  simp only [reflectXY]
  rw [Polynomial.reflect_mul p q hp hq, map_mul,
    Polynomial.reflect_mul _ _ (swap_reflect_degree p d d hpy)
      (swap_reflect_degree q e e hqy), map_mul]

theorem swap_coeff_degree {N : ℕ} (hN : 1 ≤ N) (i : ℕ) :
    ((pKernel N).coeff i).natDegree ≤ 2*N-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [← swap_coeff]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (swap_pKernel_degree hN) hj)]
  simp

/-- 实际有限系数矩阵，先有核及次数界，后取 Fin (2N) 系数。 -/
noncomputable def pMatrix (N : ℕ) : Matrix (Fin (2*N)) (Fin (2*N)) ℚ :=
  fun i j => ((pKernel N).coeff i.val).coeff j.val

end CP.Kernel

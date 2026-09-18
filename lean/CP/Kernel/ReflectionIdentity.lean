import CP.Kernel.Reflection

namespace CP.Kernel
open Polynomial

noncomputable def firstBracket (N : ℕ) : Bivariate :=
  inX ((u N).comp theta)*inY (v N)+inX ((v N).comp theta)*inY (u N)
noncomputable def secondBracket (N : ℕ) : Bivariate :=
  inX ((u N).comp theta)*inY (vStar N)-inX ((v N).comp theta)*inY (uStar N)

theorem reflect_firstBracket {N : ℕ} (hN : 1 ≤ N) :
    reflectXY (N+1) (firstBracket N) = -C (C (epsilon N))*secondBracket N := by
  unfold firstBracket
  rw [reflectXY_add, reflectXY_separated, reflectXY_separated,
    theta_u_reflect, theta_v_reflect hN]
  simp only [inX, inY, Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_C,
    secondBracket, uStar, vStar]
  ring

theorem reflect_secondBracket {N : ℕ} (hN : 1 ≤ N) :
    reflectXY (N+1) (secondBracket N) = -C (C (epsilon N))*firstBracket N := by
  unfold secondBracket
  rw [reflectXY_sub, reflectXY_separated, reflectXY_separated,
    theta_u_reflect, theta_v_reflect hN]
  simp only [uStar, vStar, reflect_twice, inX, inY,
    Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_C, firstBracket]
  ring

theorem bracket_degree_bounds {N : ℕ} (hN : 1 ≤ N) :
    (firstBracket N).natDegree ≤ N+1 ∧ (secondBracket N).natDegree ≤ N+1 ∧
    (swapXY (firstBracket N)).natDegree ≤ N+1 ∧
    (swapXY (secondBracket N)).natDegree ≤ N+1 := by
  have hu := u_degree N
  have hv := (v_degree hN).trans (Nat.le_succ _)
  have hua := (theta_comp_degree _).trans hu
  have hva := (theta_comp_degree _).trans hv
  have hus : (uStar N).natDegree ≤ N+1 := reflect_degree _ _ hu
  have hvs : (vStar N).natDegree ≤ N+1 := reflect_degree _ _ hv
  refine ⟨bracket_degree _ _ _ _ _ hua hva, bracket_sub_degree _ _ _ _ _ hua hva, ?_, ?_⟩
  · have he : swapXY (firstBracket N) =
        inX (v N)*inY ((u N).comp theta)+inX (u N)*inY ((v N).comp theta) := by
      simp only [firstBracket, map_add, map_mul, swap_inX, swap_inY]
      ring
    rw [he]
    exact bracket_degree _ _ _ _ _ hv hu
  · have he : swapXY (secondBracket N) =
        inX (vStar N)*inY ((u N).comp theta)-inX (uStar N)*inY ((v N).comp theta) := by
      simp only [secondBracket, map_sub, map_mul, swap_inX, swap_inY]
      ring
    rw [he]
    exact bracket_sub_degree _ _ _ _ _ hvs hus

theorem fNumerator_reflect {N : ℕ} (hN : 1 ≤ N) :
    reflectXY (2*N+2) (fNumerator N) = fNumerator N := by
  have he : fNumerator N = C (C (-(epsilon N / b (N+1)^2))) *
      (firstBracket N*secondBracket N) := by
    simp only [fNumerator, firstBracket, secondBracket, map_neg]
    ring
  rw [he, reflectXY_scalar, show 2*N+2 = (N+1)+(N+1) by omega]
  obtain ⟨h1, h2, h3, h4⟩ := bracket_degree_bounds hN
  rw [reflectXY_mul _ _ _ _ h1 h2 h3 h4,
    reflect_firstBracket hN, reflect_secondBracket hN]
  have hc : (C (C (epsilon N)) : Bivariate)*C (C (epsilon N)) = 1 := by
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, epsilon_sq]
    simp
  linear_combination C (C (-(epsilon N / b (N+1)^2)))*firstBracket N*secondBracket N*hc

theorem reflectXY_monomial (d i j : ℕ) :
    reflectXY d (xx^i*yy^j) = xx^(Polynomial.revAt d i)*yy^(Polynomial.revAt d j) := by
  have he := reflectXY_separated d (X^i : ℚ[X]) (X^j : ℚ[X])
  simpa [inX, inY, xx, yy] using he

theorem reflectXY_one_one : reflectXY 1 1 = xx*yy := by
  simpa [Polynomial.revAt] using reflectXY_monomial 1 0 0

theorem reflectXY_one_xx : reflectXY 1 xx = yy := by
  simpa [Polynomial.revAt] using reflectXY_monomial 1 1 0

theorem reflectXY_one_yy : reflectXY 1 yy = xx := by
  simpa [Polynomial.revAt] using reflectXY_monomial 1 0 1

theorem reflectXY_one_product : reflectXY 1 (xx*yy) = 1 := by
  simpa [Polynomial.revAt] using reflectXY_monomial 1 1 1

theorem reflectXY_pair_factors :
    reflectXY 1 (yy-xx) = -(yy-xx) ∧
    reflectXY 1 (1+xx+xx*yy) = 1+yy+xx*yy ∧
    reflectXY 1 (1+yy+xx*yy) = 1+xx+xx*yy := by
  simp only [reflectXY_sub, reflectXY_add, reflectXY_one_one, reflectXY_one_xx,
    reflectXY_one_yy, reflectXY_one_product]
  constructor
  · ring
  constructor <;> ring

theorem pair_factors_swap :
    swapXY (yy-xx) = -(yy-xx) ∧
    swapXY (1+xx+xx*yy) = 1+yy+xx*yy ∧
    swapXY (1+yy+xx*yy) = 1+xx+xx*yy := by
  simp only [map_sub, map_add, map_mul, map_one, swap_xx, swap_yy]
  constructor
  · ring
  constructor <;> ring

theorem denominator_reflect : reflectXY 3 denominator = -denominator := by
  have h0 : (yy-xx).natDegree ≤ 1 := by unfold xx yy; compute_degree <;> norm_num
  have hs0 : (swapXY (yy-xx)).natDegree ≤ 1 := by
    rw [pair_factors_swap.1, Polynomial.natDegree_neg]
    exact h0
  have hs1 : (swapXY (1+xx+xx*yy)).natDegree ≤ 1 := by
    rw [pair_factors_swap.2.1]
    exact pair_factor_degrees.2
  have hs2 : (swapXY (1+yy+xx*yy)).natDegree ≤ 1 := by
    rw [pair_factors_swap.2.2]
    exact pair_factor_degrees.1
  have hp := Polynomial.natDegree_mul_le_of_le h0 pair_factor_degrees.1
  have hsp : (swapXY ((yy-xx)*(1+xx+xx*yy))).natDegree ≤ 1+1 := by
    rw [map_mul]
    exact Polynomial.natDegree_mul_le_of_le hs0 hs1
  unfold denominator
  rw [show 3 = (1+1)+1 by rfl, reflectXY_mul _ _ _ _ hp pair_factor_degrees.2 hsp hs2,
    reflectXY_mul _ _ _ _ h0 pair_factor_degrees.1 hs0 hs1,
    reflectXY_pair_factors.1, reflectXY_pair_factors.2.1, reflectXY_pair_factors.2.2]
  ring

noncomputable def antiDiagonalPolynomial (q : ℕ) : Bivariate :=
  ∑ j ∈ Finset.range q, xx^(q-1-j)*yy^j

theorem tail_reflect (q : ℕ) :
    reflectXY (q+2) (yy^q*(1+xx+xx*yy)*(1+yy+xx*yy)) =
      xx^q*(1+xx+xx*yy)*(1+yy+xx*yy) := by
  have h1 := pair_factor_degrees.1
  have h2 := pair_factor_degrees.2
  have hs1 : (swapXY (1+xx+xx*yy)).natDegree ≤ 1 := by
    rw [pair_factors_swap.2.1]; exact h2
  have hs2 : (swapXY (1+yy+xx*yy)).natDegree ≤ 1 := by
    rw [pair_factors_swap.2.2]; exact h1
  have hf : reflectXY 2 ((1+xx+xx*yy)*(1+yy+xx*yy)) =
      (1+xx+xx*yy)*(1+yy+xx*yy) := by
    rw [show 2 = 1+1 by rfl, reflectXY_mul _ _ _ _ h1 h2 hs1 hs2,
      reflectXY_pair_factors.2.1, reflectXY_pair_factors.2.2]
    ring
  have hd : (yy^q).natDegree ≤ q := by simp [yy]
  have hs : (swapXY (yy^q)).natDegree ≤ q := by simp [xx]
  have hfd := Polynomial.natDegree_mul_le_of_le h1 h2
  have hfs : (swapXY ((1+xx+xx*yy)*(1+yy+xx*yy))).natDegree ≤ 2 := by
    rw [map_mul]
    exact Polynomial.natDegree_mul_le_of_le hs1 hs2
  rw [mul_assoc, reflectXY_mul _ _ _ _ hd hfd hs hfs, hf]
  have hm : reflectXY q (yy^q) = xx^q := by
    simpa [Polynomial.revAt] using reflectXY_monomial q 0 q
  rw [hm]
  ring

theorem pNumerator_reflect_difference {N : ℕ} (hN : 1 ≤ N) :
    pNumerator N - reflectXY (2*N+2) (pNumerator N) =
      denominator * -antiDiagonalPolynomial (2*N) := by
  rw [pNumerator, reflectXY_sub, fNumerator_reflect hN, tail_reflect]
  have hg : antiDiagonalPolynomial (2*N)*(yy-xx) = yy^(2*N)-xx^(2*N) := by
    simpa only [antiDiagonalPolynomial, mul_comm] using geom_sum₂_mul yy xx (2*N)
  unfold denominator
  linear_combination (1+xx+xx*yy)*(1+yy+xx*yy)*hg

/-- F3 的反射恒等式，等式已位于实际有限二元多项式环。 -/
theorem pKernel_reflection {N : ℕ} (hN : 1 ≤ N) :
    pKernel N + reflectXY (2*N-1) (pKernel N) = -antiDiagonalPolynomial (2*N) := by
  have hd : denominator ≠ 0 := denominator_primitive.ne_zero
  apply mul_left_cancel₀ hd
  have hdx : denominator.natDegree ≤ 3 := denominator_degree.le
  have hdy : (swapXY denominator).natDegree ≤ 3 := by
    rw [swap_denominator, Polynomial.natDegree_neg]
    exact hdx
  have hr := reflectXY_mul denominator (pKernel N) 3 (2*N-1)
    hdx (pKernel_degree hN) hdy (swap_pKernel_degree hN)
  rw [show 3+(2*N-1) = 2*N+2 by omega,
    denominator_mul_pKernel hN, denominator_reflect] at hr
  have hn := pNumerator_reflect_difference hN
  rw [hr, ← denominator_mul_pKernel hN] at hn
  linear_combination hn

theorem antiDiagonalPolynomial_coeff (q i j : ℕ) (hj : j < q) :
    ((antiDiagonalPolynomial q).coeff i).coeff j = if i = q-1-j then 1 else 0 := by
  have hc (a : ℕ) : ((if i = q-1-a then (X:ℚ[X])^a else 0).coeff j) =
      if a = j then (if i = q-1-j then 1 else 0) else 0 := by
    by_cases ha : a = j <;> by_cases hi : i = q-1-a <;>
      simp_all [Polynomial.coeff_X_pow, eq_comm]
  simp only [antiDiagonalPolynomial, xx, yy, ← Polynomial.C_pow,
    Polynomial.finset_sum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
    ite_mul, one_mul, zero_mul]
  simp_rw [hc]
  simp [hj]

/-- F3 的实际有限系数矩阵反射公式 (6.13)。 -/
theorem pMatrix_reflection {N : ℕ} (hN : 1 ≤ N) :
    pMatrix N + R (2*N)*pMatrix N*R (2*N) = -R (2*N) := by
  ext i j
  have he := congrArg (fun p : Bivariate => (p.coeff i.val).coeff j.val)
    (pKernel_reflection hN)
  simp only [Polynomial.coeff_add, Polynomial.coeff_neg, reflectXY_coeff] at he
  rw [Polynomial.revAt_le (by have := i.isLt; omega),
    Polynomial.revAt_le (by have := j.isLt; omega),
    antiDiagonalPolynomial_coeff _ _ _ j.isLt] at he
  have hh : i.val = 2*N-1-j.val ↔ i.rev = j := by
    rw [Fin.ext_iff, Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega
  simp only [hh] at he
  simpa only [Matrix.add_apply, Matrix.neg_apply, R_mul_apply, mul_R_apply,
    pMatrix, Fin.val_rev, R, Nat.sub_sub, Nat.add_comm] using he

end CP.Kernel

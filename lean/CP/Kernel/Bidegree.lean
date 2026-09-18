import CP.Kernel.Roots

namespace CP.Kernel
open Polynomial

/-- 有限二元多项式的变量交换。 -/
noncomputable def swapXY : Bivariate →+* Bivariate :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom Polynomial.C) yy

@[simp] theorem swap_inY (p : ℚ[X]) : swapXY (inY p) = inX p := by
  simp [swapXY, inY, inX]

@[simp] theorem swap_inX (p : ℚ[X]) : swapXY (inX p) = inY p := by
  have he := Polynomial.hom_eval₂ p (Polynomial.C : ℚ →+* ℚ[X])
    (Polynomial.C : ℚ[X] →+* Bivariate) (Polynomial.X : ℚ[X])
  simp only [Polynomial.eval₂_C_X] at he
  simp only [swapXY, Polynomial.coe_eval₂RingHom, inX, inY, Polynomial.eval₂_map]
  rw [he]
  have hg : (Polynomial.mapRingHom (Polynomial.C : ℚ →+* ℚ[X])).comp Polynomial.C =
      (Polynomial.C : ℚ[X] →+* Bivariate).comp Polynomial.C := by
    ext r
    simp
  rw [hg]
  rfl

@[simp] theorem swap_xx : swapXY xx = yy := by simp [swapXY, xx]
@[simp] theorem swap_yy : swapXY yy = xx := by simp [swapXY, yy, xx]
@[simp] theorem swap_constant (r : ℚ) : swapXY (C (C r)) = C (C r) := by
  simp [swapXY]

/-- 交换后的外层次数就是原来的 y 次数。 -/
theorem swap_denominator : swapXY denominator = -denominator := by
  simp only [denominator, map_mul, map_sub, map_add, map_one, swap_xx, swap_yy]
  ring

theorem denominator_degree : denominator.natDegree = 3 := by
  unfold denominator xx yy
  compute_degree <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  intro he
  have hc := congrArg (Polynomial.eval (0:ℚ)) he
  norm_num at hc

@[simp] theorem inX_degree (p : ℚ[X]) : (inX p).natDegree = p.natDegree := by
  unfold inX
  exact Polynomial.natDegree_map_eq_of_injective (f := (Polynomial.C : ℚ →+* ℚ[X])) Polynomial.C_injective p
@[simp] theorem inY_degree (p : ℚ[X]) : (inY p).natDegree = 0 := by
  exact Polynomial.natDegree_C p

/-- 一个括号在两个变量上的分别次数界，完全有限。 -/
theorem bracket_degree (p r s t : ℚ[X]) (a : ℕ)
    (hp : p.natDegree ≤ a) (hr : r.natDegree ≤ a) :
    (inX p*inY s+inX r*inY t).natDegree ≤ a := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simpa only [inX_degree, inY_degree, add_zero] using
      (Polynomial.natDegree_mul_le (p := inX p) (q := inY s)).trans (by simpa)
  · simpa only [inX_degree, inY_degree, add_zero] using
      (Polynomial.natDegree_mul_le (p := inX r) (q := inY t)).trans (by simpa)

theorem bracket_sub_degree (p r s t : ℚ[X]) (a : ℕ)
    (hp : p.natDegree ≤ a) (hr : r.natDegree ≤ a) :
    (inX p*inY s-inX r*inY t).natDegree ≤ a := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (by simpa using hp)
  · exact Polynomial.natDegree_mul_le.trans (by simpa using hr)

theorem pair_factor_degrees :
    (1+xx+xx*yy).natDegree ≤ 1 ∧ (1+yy+xx*yy).natDegree ≤ 1 := by
  constructor <;> unfold xx yy <;> compute_degree <;> norm_num

theorem fNumerator_degree {N : ℕ} (hN : 1 ≤ N) :
    (fNumerator N).natDegree ≤ 2*N+2 := by
  have hu := (theta_comp_degree (u N)).trans (u_degree N)
  have hv := (theta_comp_degree (v N)).trans ((v_degree hN).trans (Nat.le_succ _))
  have h1 := bracket_degree ((u N).comp theta) ((v N).comp theta) (v N) (u N) (N+1) hu hv
  have h2 := bracket_sub_degree ((u N).comp theta) ((v N).comp theta)
    (vStar N) (uStar N) (N+1) hu hv
  have h0 : (-C (C (epsilon N / b (N+1)^2)) : Bivariate).natDegree ≤ 0 := by simp
  have hh := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le h0 h1) h2
  simpa only [zero_add, show N+1+(N+1) = 2*N+2 by omega] using hh

theorem swap_fNumerator_degree {N : ℕ} (hN : 1 ≤ N) :
    (swapXY (fNumerator N)).natDegree ≤ 2*N+2 := by
  have hu := u_degree N
  have hv := (v_degree hN).trans (Nat.le_succ _)
  have hus : (uStar N).natDegree ≤ N+1 := reflect_degree _ _ hu
  have hvs : (vStar N).natDegree ≤ N+1 := reflect_degree _ _ hv
  have h1 := bracket_degree (v N) (u N) ((u N).comp theta) ((v N).comp theta) (N+1) hv hu
  have h2 := bracket_sub_degree (vStar N) (uStar N) ((u N).comp theta)
    ((v N).comp theta) (N+1) hvs hus
  have h0 : (-C (C (epsilon N / b (N+1)^2)) : Bivariate).natDegree ≤ 0 := by simp
  have hh := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le h0 h1) h2
  have he : swapXY (fNumerator N) = -C (C (epsilon N / b (N+1)^2)) *
      (inX (v N)*inY ((u N).comp theta)+inX (u N)*inY ((v N).comp theta)) *
      (inX (vStar N)*inY ((u N).comp theta)-inX (uStar N)*inY ((v N).comp theta)) := by
    simp only [fNumerator, map_mul, map_neg, map_add, map_sub,
      swap_constant, swap_inX, swap_inY]
    ring
  rw [he]
  simpa only [zero_add, show N+1+(N+1) = 2*N+2 by omega] using hh

theorem pNumerator_degree {N : ℕ} (hN : 1 ≤ N) :
    (pNumerator N).natDegree ≤ 2*N+2 := by
  have h0 : (yy^(2*N)).natDegree ≤ 0 := by simp [yy]
  have ht := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le h0 pair_factor_degrees.1) pair_factor_degrees.2
  unfold pNumerator
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (fNumerator_degree hN) (ht.trans (by omega)))

theorem swap_pNumerator_degree {N : ℕ} (hN : 1 ≤ N) :
    (swapXY (pNumerator N)).natDegree ≤ 2*N+2 := by
  have h0 : (xx^(2*N)).natDegree ≤ 2*N := by simp [xx]
  have ht := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le h0 pair_factor_degrees.1) pair_factor_degrees.2
  have he : swapXY (pNumerator N) = swapXY (fNumerator N) -
      xx^(2*N)*(1+xx+xx*yy)*(1+yy+xx*yy) := by
    simp only [pNumerator, map_sub, map_mul, map_pow, map_add, map_one, swap_xx, swap_yy]
    ring
  rw [he]
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (swap_fNumerator_degree hN) (ht.trans (by omega)))

theorem pKernel_degree {N : ℕ} (hN : 1 ≤ N) :
    (pKernel N).natDegree ≤ 2*N-1 := by
  by_cases hp : pKernel N = 0
  · simp [hp]
  have hd : denominator ≠ 0 := denominator_primitive.ne_zero
  have he := Polynomial.natDegree_mul hd hp
  rw [denominator_mul_pKernel hN, denominator_degree] at he
  have hb := pNumerator_degree hN
  omega

theorem swap_pKernel_degree {N : ℕ} (hN : 1 ≤ N) :
    (swapXY (pKernel N)).natDegree ≤ 2*N-1 := by
  by_cases hp : swapXY (pKernel N) = 0
  · simp [hp]
  have hd : -denominator ≠ 0 := neg_ne_zero.mpr denominator_primitive.ne_zero
  have he := Polynomial.natDegree_mul hd hp
  have hh := congrArg swapXY (denominator_mul_pKernel hN)
  rw [map_mul, swap_denominator] at hh
  rw [hh, Polynomial.natDegree_neg, denominator_degree] at he
  have hb := swap_pNumerator_degree hN
  omega

end CP.Kernel

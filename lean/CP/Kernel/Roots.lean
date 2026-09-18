import CP.Kernel.Bivariate

namespace CP.Kernel
open Polynomial

abbrev KernelField := RatFunc ℚ
noncomputable def coeffToField : ℚ[X] →+* KernelField := algebraMap _ _
noncomputable def beval (a : KernelField) : Bivariate →+* KernelField :=
  Polynomial.eval₂RingHom coeffToField a

@[simp] theorem coeffToField_eq_eval (p : ℚ[X]) :
    coeffToField p = p.eval₂ RatFunc.C RatFunc.X := by
  have he := Polynomial.hom_eval₂ p (Polynomial.C : ℚ →+* ℚ[X])
    (algebraMap ℚ[X] KernelField) (Polynomial.X : ℚ[X])
  simpa only [Polynomial.eval₂_C_X, RatFunc.algebraMap_comp_C,
    RatFunc.algebraMap_X, coeffToField] using he

@[simp] theorem beval_inX (a : KernelField) (p : ℚ[X]) :
    beval a (inX p) = p.eval₂ RatFunc.C a := by
  change (p.map Polynomial.C).eval₂ coeffToField a = _
  rw [Polynomial.eval₂_map]
  rfl

@[simp] theorem beval_inY (a : KernelField) (p : ℚ[X]) :
    beval a (inY p) = p.eval₂ RatFunc.C RatFunc.X := by
  change (Polynomial.C p).eval₂ coeffToField a = _
  rw [Polynomial.eval₂_C, coeffToField_eq_eval]

@[simp] theorem beval_xx (a : KernelField) : beval a xx = a := by
  simp [beval, xx]
@[simp] theorem beval_yy (a : KernelField) : beval a yy = RatFunc.X := by
  simp [beval, yy, coeffToField]
@[simp] theorem beval_constant (a : KernelField) (r : ℚ) :
    beval a (Polynomial.C (Polynomial.C r)) = RatFunc.C r := by
  simp [beval, coeffToField]

theorem field_one_add_ne_zero : (1+RatFunc.X : KernelField) ≠ 0 := by
  have he := RatFunc.algebraMap_ne_zero one_add_X_ne_zero
  simpa only [map_add, map_one, RatFunc.algebraMap_X] using he

theorem field_quadratic_ne_zero :
    (RatFunc.X^2+RatFunc.X+1 : KernelField) ≠ 0 := by
  have hp : (X^2+X+1 : ℚ[X]) ≠ 0 := by
    intro he
    have hc := congrArg (fun p : ℚ[X] => p.coeff 2) he
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X] at hc
  have he := RatFunc.algebraMap_ne_zero hp
  simpa only [map_add, map_pow, map_one, RatFunc.algebraMap_X] using he

theorem pNumerator_first_pair_root {N : ℕ} (hN : 1 ≤ N) :
    beval (-1/(1+RatFunc.X)) (pNumerator N) = 0 := by
  let y : KernelField := RatFunc.X
  have ht : 1+y ≠ 0 := field_one_add_ne_zero
  have hu := congrArg (Polynomial.eval₂ (RatFunc.C : ℚ →+* KernelField) y)
    (sigma_theta_u N)
  have hv := congrArg (Polynomial.eval₂ (RatFunc.C : ℚ →+* KernelField) y)
    (sigma_theta_v hN)
  rw [sigmaPullback_eval₂ _ _ _ ((theta_comp_degree _).trans (u_degree N)) _ ht,
    Polynomial.eval₂_neg] at hu
  rw [sigmaPullback_eval₂ _ _ _ ((theta_comp_degree _).trans
    ((v_degree hN).trans (Nat.le_succ _))) _ ht] at hv
  simp only [Nat.succ_eq_add_one] at hv
  have hb : ((u N).comp theta).eval₂ RatFunc.C (-1/(1+y)) * (v N).eval₂ RatFunc.C y +
      ((v N).comp theta).eval₂ RatFunc.C (-1/(1+y)) * (u N).eval₂ RatFunc.C y = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero (N+1) ht)
    linear_combination (v N).eval₂ RatFunc.C y*hu + (u N).eval₂ RatFunc.C y*hv
  have hz : 1+(-1/(1+y))+(-1/(1+y))*y = 0 := by field_simp <;> ring
  change beval (-1/(1+y)) (pNumerator N) = 0
  simp only [pNumerator, fNumerator, map_sub, map_mul, map_neg, map_add,
    map_pow, map_one, beval_constant, beval_inX, beval_inY, beval_xx, beval_yy]
  change -RatFunc.C (epsilon N / b (N+1)^2) *
    (((u N).comp theta).eval₂ RatFunc.C (-1/(1+y)) * (v N).eval₂ RatFunc.C y +
      ((v N).comp theta).eval₂ RatFunc.C (-1/(1+y)) * (u N).eval₂ RatFunc.C y) * _ -
      y^(2*N)*(1+(-1/(1+y))+(-1/(1+y))*y)*_ = 0
  rw [hb, hz]
  ring

theorem pNumerator_second_pair_root {N : ℕ} (hN : 1 ≤ N) :
    beval (-(1+RatFunc.X)/RatFunc.X) (pNumerator N) = 0 := by
  let y : KernelField := RatFunc.X
  have hy : y ≠ 0 := RatFunc.X_ne_zero
  have ha : -1-(-(1+y)/y) = y⁻¹ := by field_simp <;> ring
  have hu := reflect_eval₂ (RatFunc.C : ℚ →+* KernelField) (u N) (N+1) (u_degree N) y hy
  have hv := reflect_eval₂ (RatFunc.C : ℚ →+* KernelField) (v N) (N+1)
    ((v_degree hN).trans (Nat.le_succ _)) y hy
  change (uStar N).eval₂ RatFunc.C y = _ at hu
  change (vStar N).eval₂ RatFunc.C y = _ at hv
  have hb : ((u N).comp theta).eval₂ RatFunc.C (-(1+y)/y) * (vStar N).eval₂ RatFunc.C y -
      ((v N).comp theta).eval₂ RatFunc.C (-(1+y)/y) * (uStar N).eval₂ RatFunc.C y = 0 := by
    simp only [Polynomial.eval₂_comp, theta, Polynomial.eval₂_sub, Polynomial.eval₂_neg,
      Polynomial.eval₂_one, Polynomial.eval₂_X, ha]
    rw [hu, hv]
    ring
  have hz : 1+y+(-(1+y)/y)*y = 0 := by field_simp <;> ring
  change beval (-(1+y)/y) (pNumerator N) = 0
  simp only [pNumerator, fNumerator, map_sub, map_mul, map_neg, map_add,
    map_pow, map_one, beval_constant, beval_inX, beval_inY, beval_xx, beval_yy]
  change -RatFunc.C (epsilon N / b (N+1)^2) * _ *
    (((u N).comp theta).eval₂ RatFunc.C (-(1+y)/y) * (vStar N).eval₂ RatFunc.C y -
      ((v N).comp theta).eval₂ RatFunc.C (-(1+y)/y) * (uStar N).eval₂ RatFunc.C y) -
      y^(2*N)*_*(1+y+(-(1+y)/y)*y) = 0
  rw [hb, hz]
  ring

theorem pNumerator_diagonal_field {N : ℕ} (hN : 1 ≤ N) :
    beval RatFunc.X (pNumerator N) = 0 := by
  change (pNumerator N).eval₂ coeffToField
    (coeffToField (Polynomial.X : ℚ[X])) = 0
  rw [Polynomial.eval₂_at_apply, pNumerator_diagonal hN, map_zero]

theorem denominator_field_factor :
    denominator.map coeffToField =
      C (-(1+RatFunc.X)*RatFunc.X) *
        ((X-C RatFunc.X)*(X-C (-1/(1+RatFunc.X)))*
          (X-C (-(1+RatFunc.X)/RatFunc.X))) := by
  let y : KernelField := RatFunc.X
  have ht : 1+y ≠ 0 := field_one_add_ne_zero
  have hy : y ≠ 0 := RatFunc.X_ne_zero
  have hc1 : (C (1+y) : Polynomial KernelField)*C (-1/(1+y)) = -1 := by
    rw [← Polynomial.C_mul]
    have h : (1+y)*(-1/(1+y)) = -1 := by field_simp
    rw [h]
    simp
  have hc2 : (C y : Polynomial KernelField)*C (-(1+y)/y) = -C (1+y) := by
    rw [← Polynomial.C_mul]
    have h : y*(-(1+y)/y) = -(1+y) := by field_simp
    rw [h, Polynomial.C_neg]
  have h1 : (1+X+X*C y : Polynomial KernelField) = C (1+y)*(X-C (-1/(1+y))) := by
    simp only [map_add, map_one] at hc1 ⊢
    linear_combination hc1
  have h2 : (1+C y+X*C y : Polynomial KernelField) = C y*(X-C (-(1+y)/y)) := by
    simp only [map_add, map_one] at hc2 ⊢
    linear_combination hc2
  simp only [denominator, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_one, xx, yy, Polynomial.map_X, Polynomial.map_C,
    coeffToField, RatFunc.algebraMap_X]
  change (C y-X)*(1+X+X*C y)*(1+C y+X*C y) =
    C (-(1+y)*y)*((X-C y)*(X-C (-1/(1+y)))*(X-C (-(1+y)/y)))
  rw [h1, h2]
  simp only [map_mul, map_neg]
  ring

theorem field_three_roots_distinct :
    (RatFunc.X : KernelField) ≠ -1/(1+RatFunc.X) ∧
    (RatFunc.X : KernelField) ≠ -(1+RatFunc.X)/RatFunc.X ∧
    (-1/(1+RatFunc.X) : KernelField) ≠ -(1+RatFunc.X)/RatFunc.X := by
  let y : KernelField := RatFunc.X
  have hy : y ≠ 0 := RatFunc.X_ne_zero
  have ht : 1+y ≠ 0 := field_one_add_ne_zero
  have hq : y^2+y+1 ≠ 0 := field_quadratic_ne_zero
  change y ≠ -1/(1+y) ∧ y ≠ -(1+y)/y ∧ -1/(1+y) ≠ -(1+y)/y
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply hq
    field_simp [ht] at he
    linear_combination he
  · intro he
    apply hq
    field_simp [hy] at he
    linear_combination he
  · intro he
    apply hq
    field_simp [hy, ht] at he
    linear_combination he

/-- 三个根的消去合并为完整分母的整除；交点不构成例外。 -/
theorem denominator_dvd_pNumerator {N : ℕ} (hN : 1 ≤ N) :
    denominator ∣ pNumerator N := by
  apply primitive_dvd_of_fraction_dvd denominator_primitive
  let p := (pNumerator N).map coeffToField
  have h0 : (X-C RatFunc.X : Polynomial KernelField) ∣ p := by
    apply Polynomial.dvd_iff_isRoot.mpr
    change p.eval RatFunc.X = 0
    dsimp only [p]
    rw [Polynomial.eval_map]
    exact pNumerator_diagonal_field hN
  have h1 : (X-C (-1/(1+RatFunc.X)) : Polynomial KernelField) ∣ p := by
    apply Polynomial.dvd_iff_isRoot.mpr
    change p.eval (-1/(1+RatFunc.X)) = 0
    dsimp only [p]
    rw [Polynomial.eval_map]
    exact pNumerator_first_pair_root hN
  have h2 : (X-C (-(1+RatFunc.X)/RatFunc.X) : Polynomial KernelField) ∣ p := by
    apply Polynomial.dvd_iff_isRoot.mpr
    change p.eval (-(1+RatFunc.X)/RatFunc.X) = 0
    dsimp only [p]
    rw [Polynomial.eval_map]
    exact pNumerator_second_pair_root hN
  obtain ⟨hd01, hd02, hd12⟩ := field_three_roots_distinct
  have hc01 := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hd01).isUnit
  have hc02 := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hd02).isUnit
  have hc12 := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hd12).isUnit
  obtain ⟨r, hr⟩ := (hc02.mul_left hc12).mul_dvd (hc01.mul_dvd h0 h1) h2
  let c : KernelField := -(1+RatFunc.X)*RatFunc.X
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr field_one_add_ne_zero) RatFunc.X_ne_zero
  change denominator.map coeffToField ∣ p
  refine ⟨C c⁻¹*r, ?_⟩
  rw [denominator_field_factor]
  change p = C c * _ * (C c⁻¹*r)
  rw [hr]
  have hu : (C c : Polynomial KernelField)*C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  linear_combination -((X-C RatFunc.X)*(X-C (-1/(1+RatFunc.X)))*
    (X-C (-(1+RatFunc.X)/RatFunc.X)))*r*hu

/-- 取经整除定理保证存在的商；N=0 仅总化定义，正阶定理不使用它。 -/
noncomputable def pKernel (N : ℕ) : Bivariate :=
  if hN : 1 ≤ N then Classical.choose (denominator_dvd_pNumerator hN) else 0

theorem denominator_mul_pKernel {N : ℕ} (hN : 1 ≤ N) :
    denominator * pKernel N = pNumerator N := by
  unfold pKernel
  rw [dif_pos hN]
  exact (Classical.choose_spec (denominator_dvd_pNumerator hN)).symm

end CP.Kernel

import CP.Kernel.Odd.NullPolynomial

namespace CP.Kernel
open Polynomial CP.Fractional

set_option maxHeartbeats 1000000

theorem normalizedP_fractional (N : ℕ) (x : ℚ) (ht : 1+x ≠ 0) :
    (normalizedP N).eval (x/(1+x)) =
      (1+x)^(N+1)*(normalizedP N).eval (-x)-
      (-1)^N*x^(2*N+1)/(1+x)^N*(normalizedP N).eval (1+x) := by
  have hx : -x ≠ 1 := by intro he; apply ht; linear_combination -he
  have he := fractional_substitution (N+1) (by omega) (-x) hx
  have hden : -x-1 ≠ 0 := by intro he; apply ht; linear_combination -he
  have ha : -x/(-x-1) = x/(1+x) := by field_simp [ht, hden]; ring
  simp only [phi, Nat.add_sub_cancel, show 2*(N+1)-1 = 2*N+1 by omega,
    sub_neg_eq_add, ha] at he
  have hs : (-x)^(2*N+1) = -x^(2*N+1) := by
    rw [neg_pow, pow_add, pow_mul]
    norm_num
  rw [hs] at he
  simp only [normalizedP, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination (b (N+1))⁻¹*he

/-- (7.4) 的实际有限多项式清分母版本。 -/
theorem nu_sigma_polynomial (N : ℕ) :
    sigmaPullback (2*N) (nuPolynomial N) =
      C ((-1:ℚ)^N)*(1+X)^(2*N+1)*((normalizedP N).comp (-X))^2 -
      X^(2*N+1)*(normalizedP N).comp (1+X)*(normalizedP N).comp (-X) := by
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  have ht : 1+x ≠ 0 := by intro he; apply hx1; linear_combination he
  have hs : (-1/(1+x):ℚ) ≠ 0 := div_ne_zero (by norm_num) ht
  rw [sigmaPullback_eval _ _ (nuPolynomial_degree N) _ hx1,
    nuPolynomial_factor, Polynomial.eval_mul]
  simp only [sigma]
  rw [reflect_eval _ _ (shiftedP_degree N) _ hs]
  have he1 : 1+(-1/(1+x)) = x/(1+x) := by field_simp
  have he2 : 1+(-1/(1+x))⁻¹ = -x := by field_simp
  simp only [shiftedP, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, he1, he2]
  rw [normalizedP_fractional N x ht]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_neg]
  have hsign : (-1:ℚ)^N*(-1)^N = 1 := by rw [← mul_pow]; norm_num
  rw [div_pow, show 2*N = N+N by omega]
  simp only [pow_add, pow_succ]
  field_simp [ht, pow_ne_zero N ht]
  linear_combination -(normalizedP N).eval (1+x)*(normalizedP N).eval (-x)*
    x^N*x^N*x*hsign

/-- 单位中心坐标：ν_N 是一个非零多项式系数向量的平方范数。 -/
theorem nu_center_pos (N : ℕ) : 0 < nu N ⟨N, by omega⟩ := by
  have hsum : (nuPolynomial N).coeff N =
      ∑ a ∈ Finset.range (N+1), ((shiftedP N).coeff a)^2 := by
    rw [nuPolynomial_factor, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ N := by have := Finset.mem_range.mp ha; omega
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega), Nat.sub_sub_self ha', pow_two]
  change 0 < (nuPolynomial N).coeff N
  rw [hsum]
  have hp : shiftedP N ≠ 0 := by
    intro he
    have hh := shiftedP_eval_neg_one N
    rw [he, Polynomial.eval_zero] at hh
    exact zero_ne_one hh
  apply Finset.sum_pos'
  · intro a ha
    exact sq_nonneg _
  · refine ⟨(shiftedP N).natDegree, Finset.mem_range.mpr (by have := shiftedP_degree N; omega), ?_⟩
    exact sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)

end CP.Kernel

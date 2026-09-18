import CP.Kernel.Odd.NullSubstitution
import CP.Kernel.Odd.SigmaSeries

namespace CP.Kernel
open Polynomial Matrix Finset CP.Series

noncomputable def univariateSeries : ℚ[X] →+* KernelSeries :=
  polynomialSeries.comp (Polynomial.mapRingHom Polynomial.C)

theorem univariateSeries_apply (p : ℚ[X]) : univariateSeries p = polynomialSeries (inX p) := rfl
@[simp] theorem univariateSeries_X : univariateSeries X = PowerSeries.X := by
  rw [univariateSeries_apply, polynomialSeries_evalXY, evalXY_inX]
  simp
@[simp] theorem univariateSeries_C (a : ℚ) :
    univariateSeries (C a) = PowerSeries.C KernelField (RatFunc.C a) := by
  rw [univariateSeries_apply, polynomialSeries_evalXY, evalXY_inX]
  simp

noncomputable def nuImage (N : ℕ) : ℚ[X] := C ((-1:ℚ)^N)*((normalizedP N).comp (-X))^2

/-- (7.4) 的精确级数公式，首个可能的余项次数为 2N+1。 -/
theorem nu_series_exact (N : ℕ) :
    negPower KernelField 1*substitutedSeries (inX (nuPolynomial N)) =
      univariateSeries (nuImage N)-PowerSeries.X^(2*N+1)*
        (negPower KernelField (2*N+1)*univariateSeries
          ((normalizedP N).comp (1+X)*(normalizedP N).comp (-X))) := by
  let t : KernelSeries := 1+PowerSeries.X
  let z := negPower KernelField (2*N+1)
  let a := substitutedSeries (inX (nuPolynomial N))
  have hz : t^(2*N+1)*z = 1 := by
    simpa only [zero_add,pow_zero] using negPower_cancel KernelField 0 (2*N+1)
  have ht : t*negPower KernelField 1 = 1 := negPower_one_inverse KernelField
  have he := congrArg univariateSeries (nu_sigma_polynomial N)
  rw [univariateSeries_apply, sigmaPullback_series _ _ (nuPolynomial_degree N)] at he
  have hm : univariateSeries (C ((-1:ℚ)^N)*(1+X)^(2*N+1)*((normalizedP N).comp (-X))^2 -
      X^(2*N+1)*(normalizedP N).comp (1+X)*(normalizedP N).comp (-X)) =
      t^(2*N+1)*univariateSeries (nuImage N)-PowerSeries.X^(2*N+1)*univariateSeries
        ((normalizedP N).comp (1+X)*(normalizedP N).comp (-X)) := by
    simp only [nuImage, map_sub,map_mul,map_pow,map_add,map_one,univariateSeries_X]
    dsimp only [t]
    ring
  rw [hm] at he
  have hta : t^(2*N+1)*(negPower KernelField 1*a) = t^(2*N)*a := by
    rw [pow_succ]
    linear_combination t^(2*N)*a*ht
  change negPower KernelField 1*a = _
  change t^(2*N)*a = _ at he
  rw [← hta] at he
  linear_combination z*he + (univariateSeries (nuImage N)-negPower KernelField 1*a)*hz

/-- 实际 ν 的 G 像；只取严格低于余项首次数的有限坐标。 -/
theorem G_nu (N : ℕ) : G (2*N+1) *ᵥ nu N = fun i => (nuImage N).coeff i.val := by
  funext i
  have he := congrArg (PowerSeries.coeff KernelField i.val) (nu_series_exact N)
  rw [G_vector_series _ (by have := nuPolynomial_degree N; omega), map_sub,
    univariateSeries_apply, polynomialSeries_inX_coeff, remainder_coeff_zero _ i.isLt, sub_zero] at he
  exact RatFunc.C.injective he

theorem nuImage_degree (N : ℕ) : (nuImage N).natDegree ≤ 2*N := by
  have hd : ((normalizedP N).comp (-X)).natDegree ≤ N := by
    have hg : (-X : ℚ[X]).natDegree ≤ 1 := by simp
    exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul (normalizedP_degree N) hg).trans (by omega))
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (Polynomial.natDegree_pow_le.trans (by omega))

theorem nuImage_reflect (N : ℕ) : (nuImage N).reflect (2*N) = nuImage N := by
  have hd : (((normalizedP N).comp (-X))^2).natDegree ≤ 2*N := by
    have hb : ((normalizedP N).comp (-X)).natDegree ≤ N := by
      exact Polynomial.natDegree_comp_le.trans
        ((Nat.mul_le_mul (normalizedP_degree N) (by simp : (-X:ℚ[X]).natDegree ≤ 1)).trans (by omega))
    exact Polynomial.natDegree_pow_le.trans (by omega)
  unfold nuImage
  rw [Polynomial.reflect_C_mul]
  congr 1
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  rw [reflect_eval _ _ hd x hx]
  have hh := congrArg (Polynomial.eval (-x)) (normalizedP_reflect N)
  rw [reflect_eval _ _ (normalizedP_degree N) (-x) (neg_ne_zero.mpr hx)] at hh
  simp only [Polynomial.eval_pow, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
  rw [inv_neg] at hh
  rw [← hh]
  rw [mul_pow, ← pow_mul, neg_pow, show N*2 = 2*N by omega,
    show (-1:ℚ)^(2*N) = 1 by rw [pow_mul]; norm_num]
  ring

theorem nuImage_reversal (N : ℕ) :
    R (2*N+1) *ᵥ (fun i => (nuImage N).coeff i.val) = fun i => (nuImage N).coeff i.val := by
  funext i
  have he := congrArg (fun p : ℚ[X] => p.coeff i.val) (nuImage_reflect N)
  simp only [Polynomial.coeff_reflect] at he
  rw [Polynomial.revAt_le (by have := i.isLt; omega)] at he
  change (∑ j, (if i.rev = j then (1:ℚ) else 0)*(nuImage N).coeff j.val) = _
  simp only [ite_mul,one_mul,zero_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hi : i.rev.val = 2*N-i.val := by rw [Fin.val_rev]; omega
  rw [hi]
  exact he

/-- O2：规范中的实际向量确实属于奇数 Ω 的零空间。 -/
theorem omega_nu_zero (N : ℕ) : omega (2*N+1) *ᵥ nu N = 0 := by
  rw [omega, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, nu_reversal,
    ← Matrix.mulVec_mulVec, G_nu, nuImage_reversal, sub_self]

end CP.Kernel

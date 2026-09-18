import CP.Kernel.ActualC
import Mathlib.RingTheory.Localization.FractionRing

namespace CP.Kernel
open Polynomial Finset Matrix CP.Series

abbrev KernelSeries := PowerSeries KernelField

/-- 仅 x 是形式变量；y 已进入系数域 Q(y)。 -/
noncomputable def polynomialSeries : Bivariate →+* KernelSeries :=
  (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom coeffToField)

noncomputable def substitutedSeries (p : Bivariate) : KernelSeries :=
  p.eval₂ ((PowerSeries.C KernelField).comp coeffToField) (-negPower KernelField 1)

@[simp] theorem polynomialSeries_coeff (p : Bivariate) (i : ℕ) :
    PowerSeries.coeff KernelField i (polynomialSeries p) = coeffToField (p.coeff i) := by
  simp [polynomialSeries, Polynomial.coeff_coe]

theorem polynomialSeries_evalXY (p : Bivariate) :
    polynomialSeries p = evalXY ((PowerSeries.C KernelField).comp RatFunc.C)
      PowerSeries.X (PowerSeries.C KernelField RatFunc.X) p := by
  have he (a : ℚ[X]) :
      PowerSeries.C KernelField (coeffToField a) =
      a.eval₂ ((PowerSeries.C KernelField).comp RatFunc.C) (PowerSeries.C KernelField RatFunc.X) := by
    rw [coeffToField_eq_eval]
    exact Polynomial.hom_eval₂ a RatFunc.C (PowerSeries.C KernelField) RatFunc.X
  have hh : (PowerSeries.C KernelField).comp coeffToField =
      Polynomial.eval₂RingHom ((PowerSeries.C KernelField).comp RatFunc.C)
        (PowerSeries.C KernelField RatFunc.X) := RingHom.ext he
  change ((p.map coeffToField : Polynomial KernelField) : KernelSeries) = _
  rw [← Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_map, hh]
  rfl

theorem substitutedSeries_evalXY (p : Bivariate) :
    substitutedSeries p = evalXY ((PowerSeries.C KernelField).comp RatFunc.C)
      (-negPower KernelField 1) (PowerSeries.C KernelField RatFunc.X) p := by
  have he (a : ℚ[X]) :
      PowerSeries.C KernelField (coeffToField a) =
      a.eval₂ ((PowerSeries.C KernelField).comp RatFunc.C) (PowerSeries.C KernelField RatFunc.X) := by
    rw [coeffToField_eq_eval]
    exact Polynomial.hom_eval₂ a RatFunc.C (PowerSeries.C KernelField) RatFunc.X
  have hh : (PowerSeries.C KernelField).comp coeffToField =
      Polynomial.eval₂RingHom ((PowerSeries.C KernelField).comp RatFunc.C)
        (PowerSeries.C KernelField RatFunc.X) := RingHom.ext he
  simp only [substitutedSeries, evalXY, Polynomial.coe_eval₂RingHom, hh]

/-- 有限多项式代换的逐项展开，不使用无限矩阵。 -/
theorem substitutedSeries_expansion {q : ℕ} (p : Bivariate) (hp : p.natDegree < q) :
    negPower KernelField 1*substitutedSeries p =
      ∑ j : Fin q, PowerSeries.C KernelField ((-1)^j.val*coeffToField (p.coeff j.val))*
        negPower KernelField (j.val+1) := by
  unfold substitutedSeries
  rw [Polynomial.eval₂_eq_sum_range' _ hp, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => PowerSeries.C KernelField ((-1)^j*coeffToField (p.coeff j))*negPower KernelField (j+1)) q]
  apply Finset.sum_congr rfl
  intro j hj
  rw [negPower_eq_pow KernelField (j+1), pow_succ, neg_pow]
  simp only [RingHom.comp_apply, map_mul, map_pow, map_neg, map_one]
  ring

theorem substitutedSeries_coeff {q : ℕ} (p : Bivariate) (hp : p.natDegree < q) (i : ℕ) :
    PowerSeries.coeff KernelField i (negPower KernelField 1*substitutedSeries p) =
      coeffToField (∑ j : Fin q, C ((-1:ℚ)^(i+j.val)*((i+j.val).choose i:ℚ))*p.coeff j.val) := by
  rw [substitutedSeries_expansion p hp]
  simp only [map_sum, PowerSeries.coeff_C_mul, negPower_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [coeffToField, RatFunc.algebraMap_C, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_ratCast, pow_add]
  ring

/-- 实际 C 系数与 G 的有限矩阵乘法完全对应。 -/
theorem G_cMatrix_series {N : ℕ} (hN : 1 ≤ N) (i : Fin (2*N)) :
    PowerSeries.coeff KernelField i.val (negPower KernelField 1*substitutedSeries (cKernel N)) =
      coeffToField (∑ k : Fin (2*N), C (G (2*N) i k)*(cKernel N).coeff k.val) := by
  exact substitutedSeries_coeff _ (by have := cKernel_degree hN; omega) _

theorem G_cMatrix_coeff {N : ℕ} (i j : Fin (2*N)) :
    (∑ k : Fin (2*N), C (G (2*N) i k)*(cKernel N).coeff k.val).coeff j.val =
      (G (2*N)*cMatrix N) i j := by
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Matrix.mul_apply, cMatrix]

/-- 每个低于 q 的余项系数确实为零。 -/
theorem remainder_coeff_zero (r : KernelSeries) {q i : ℕ} (hi : i < q) :
    PowerSeries.coeff KernelField i (PowerSeries.X^q*r) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

end CP.Kernel

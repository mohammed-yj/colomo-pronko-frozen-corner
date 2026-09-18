import CP.Kernel.DescentAlgebra
import CP.Kernel.SeriesCoefficients

namespace CP.Kernel
open Polynomial Finset Matrix CP.Series

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

theorem hom_evalXY {F H : Type*} [CommRing F] [CommRing H]
    (f : ℚ →+* F) (g : F →+* H) (x y : F) (p : Bivariate) :
    g (evalXY f x y p) = evalXY (g.comp f) (g x) (g y) p := by
  have he := Polynomial.hom_eval₂ p (Polynomial.eval₂RingHom f y) g x
  have hh : g.comp (Polynomial.eval₂RingHom f y) = Polynomial.eval₂RingHom (g.comp f) (g y) := by
    apply RingHom.ext
    intro a
    exact Polynomial.hom_eval₂ a f g y
  simpa only [evalXY, Polynomial.coe_eval₂RingHom, hh] using he

abbrev SeriesFractionField := FractionRing KernelSeries
noncomputable def seriesToField : KernelSeries →+* SeriesFractionField := algebraMap _ _

theorem seriesToField_injective : Function.Injective seriesToField :=
  IsFractionRing.injective KernelSeries SeriesFractionField

theorem polynomialSeries_denominator_constant :
    PowerSeries.constantCoeff KernelField (polynomialSeries denominator) =
      RatFunc.X*(1+RatFunc.X) := by
  rw [polynomialSeries_evalXY]
  simp only [denominator, map_mul, map_add, map_sub, map_one, evalXY_xx, evalXY_yy,
    PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, sub_zero, add_zero, zero_mul, one_mul, mul_one]

theorem polynomialSeries_denominator_unit :
    PowerSeries.constantCoeff KernelField (polynomialSeries denominator) ≠ 0 := by
  rw [polynomialSeries_denominator_constant]
  exact mul_ne_zero RatFunc.X_ne_zero field_one_add_ne_zero

/-- 从已证有理函数恒等式运输到幂级数环中的清分母恒等式。
分式域仅用于忠实运输；最终等式本身在 Q(y)[[x]]。 -/
theorem cKernel_series_cleared {N : ℕ} (hN : 1 ≤ N) :
    (1+PowerSeries.X : KernelSeries)^(2*N)*polynomialSeries denominator *
      (negPower KernelField 1*substitutedSeries (cKernel N)-polynomialSeries (pKernel N)) +
      (PowerSeries.C KernelField RatFunc.X-PowerSeries.X)*
        (1+PowerSeries.C KernelField RatFunc.X+PowerSeries.X*PowerSeries.C KernelField RatFunc.X) =
      PowerSeries.X^(2*N)*polynomialSeries (descentRemainder N) := by
  let f := (PowerSeries.C KernelField).comp RatFunc.C
  let g := seriesToField
  let x := g (PowerSeries.X : KernelSeries)
  let y := g (PowerSeries.C KernelField RatFunc.X)
  have hz : (1+x)*g (negPower KernelField 1) = 1 := by
    have he := congrArg g (negPower_one_inverse KernelField)
    simpa only [map_mul, map_add, map_one] using he
  have ht : 1+x ≠ 0 := by intro he; rw [he, zero_mul] at hz; exact zero_ne_one hz
  have hg : g (negPower KernelField 1) = (1+x)⁻¹ := by
    apply (mul_left_cancel₀ ht)
    rw [hz, mul_inv_cancel₀ ht]
  have hn := cKernel_sigma_cleared (g.comp f) hN x y ht
  apply seriesToField_injective
  simp only [map_add, map_sub, map_mul, map_pow, map_one]
  rw [polynomialSeries_evalXY, polynomialSeries_evalXY, polynomialSeries_evalXY,
    substitutedSeries_evalXY]
  simp only [hom_evalXY, map_neg]
  change (1+x)^(2*N)*evalXY (g.comp f) x y denominator *
    (g (negPower KernelField 1)*evalXY (g.comp f) (-g (negPower KernelField 1)) y (cKernel N)-
      evalXY (g.comp f) x y (pKernel N)) + (y-x)*(1+y+x*y) =
      x^(2*N)*evalXY (g.comp f) x y (descentRemainder N)
  rw [hg]
  simpa only [div_eq_mul_inv, neg_mul, one_mul, mul_comm] using hn

noncomputable def kernelSeries (q : ℕ) : KernelSeries :=
  PowerSeries.map coeffToField (rationalKernel q)

theorem kernelSeries_denominator (q : ℕ) :
    (1+PowerSeries.X : KernelSeries)^q*
      (1+PowerSeries.X+PowerSeries.X*PowerSeries.C KernelField RatFunc.X)*kernelSeries q = 1 := by
  have he := congrArg (PowerSeries.map coeffToField) (rationalKernel_denominator q)
  simpa only [map_mul, map_pow, map_add, map_one, PowerSeries.map_X,
    PowerSeries.map_C, coeffToField, RatFunc.algebraMap_X] using he

noncomputable def exactRemainder (N : ℕ) : KernelSeries :=
  negPower KernelField (2*N)*(polynomialSeries denominator)⁻¹*
    polynomialSeries (descentRemainder N)

/-- (6.14)–(6.15) 的精确级数恒等式，显式保留 X^(2N) 余项。 -/
theorem cKernel_series_exact {N : ℕ} (hN : 1 ≤ N) :
    negPower KernelField 1*substitutedSeries (cKernel N) =
      polynomialSeries (pKernel N)-kernelSeries (2*N)+PowerSeries.X^(2*N)*exactRemainder N := by
  let t : KernelSeries := 1+PowerSeries.X
  let d := polynomialSeries denominator
  let z := negPower KernelField (2*N)*d⁻¹
  have ht : t^(2*N)*negPower KernelField (2*N) = 1 := by
    simpa only [zero_add, pow_zero] using negPower_cancel KernelField 0 (2*N)
  have hd : d*d⁻¹ = 1 := PowerSeries.mul_inv_cancel _ polynomialSeries_denominator_unit
  have hz : (t^(2*N)*d)*z = 1 := by
    calc
      _ = (t^(2*N)*negPower KernelField (2*N))*(d*d⁻¹) := by dsimp [z]; ring
      _ = _ := by rw [ht,hd,one_mul]
  have htail : t^(2*N)*d*kernelSeries (2*N) =
      (PowerSeries.C KernelField RatFunc.X-PowerSeries.X)*
      (1+PowerSeries.C KernelField RatFunc.X+PowerSeries.X*PowerSeries.C KernelField RatFunc.X) := by
    have hk := kernelSeries_denominator (2*N)
    have hde : d = (PowerSeries.C KernelField RatFunc.X-PowerSeries.X)*
        (1+PowerSeries.X+PowerSeries.X*PowerSeries.C KernelField RatFunc.X)*
        (1+PowerSeries.C KernelField RatFunc.X+PowerSeries.X*PowerSeries.C KernelField RatFunc.X) := by
      dsimp only [d]
      rw [polynomialSeries_evalXY]
      simp only [denominator, map_mul, map_sub, map_add, map_one, evalXY_xx, evalXY_yy]
    rw [hde]
    linear_combination (PowerSeries.C KernelField RatFunc.X-PowerSeries.X)*
      (1+PowerSeries.C KernelField RatFunc.X+PowerSeries.X*PowerSeries.C KernelField RatFunc.X)*hk
  have hc := cKernel_series_cleared hN
  change t^(2*N)*d*(_-_) + _ = _ at hc
  rw [← htail] at hc
  change negPower KernelField 1*substitutedSeries (cKernel N) =
    polynomialSeries (pKernel N)-kernelSeries (2*N)+
    PowerSeries.X^(2*N)*(z*polynomialSeries (descentRemainder N))
  linear_combination z*hc +
    (polynomialSeries (pKernel N)-kernelSeries (2*N)-
      negPower KernelField 1*substitutedSeries (cKernel N))*hz

/-- 所有 i<2N 的低次系数，余项已由一般定理消去。 -/
theorem cKernel_series_low_coeff {N : ℕ} (hN : 1 ≤ N) (i : Fin (2*N)) :
    PowerSeries.coeff KernelField i.val (negPower KernelField 1*substitutedSeries (cKernel N)) =
      coeffToField ((pKernel N).coeff i.val)-
        coeffToField (PowerSeries.coeff ℚ[X] i.val (rationalKernel (2*N))) := by
  rw [cKernel_series_exact hN, map_add, map_sub, polynomialSeries_coeff,
    remainder_coeff_zero _ i.isLt, add_zero]
  rw [kernelSeries, PowerSeries.coeff_map]

/-- F4：(6.15) 是实际多项式核的有限矩阵等式。 -/
theorem G_cMatrix {N : ℕ} (hN : 1 ≤ N) :
    G (2*N)*cMatrix N = pMatrix N+G (2*N)*R (2*N)*(G (2*N))⁻¹ := by
  ext i j
  have he := cKernel_series_low_coeff hN i
  rw [G_cMatrix_series hN, ← map_sub] at he
  have hinj : Function.Injective coeffToField := IsFractionRing.injective ℚ[X] KernelField
  have hp := hinj he
  have hc := congrArg (fun p : ℚ[X] => p.coeff j.val) hp
  dsimp only at hc
  rw [G_cMatrix_coeff, Polynomial.coeff_sub] at hc
  simpa only [Matrix.add_apply, pMatrix, even_G_R_inverse_kernel hN, sub_eq_add_neg] using hc

end CP.Kernel

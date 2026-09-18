import CP.Kernel.ExactTruncation

namespace CP.Kernel
open Polynomial Matrix CP.Series

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

/-- 有限齐次代换运输至 Q(y)[[x]]；只使用 1+x 的可逆性。 -/
theorem sigmaPullback_series (d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d) :
    polynomialSeries (inX (sigmaPullback d p)) =
      (1+PowerSeries.X : KernelSeries)^d*substitutedSeries (inX p) := by
  let f := (PowerSeries.C KernelField).comp RatFunc.C
  let g := seriesToField
  let x := g (PowerSeries.X : KernelSeries)
  have hz : (1+x)*g (negPower KernelField 1) = 1 := by
    simpa only [map_mul, map_add, map_one] using congrArg g (negPower_one_inverse KernelField)
  have ht : 1+x ≠ 0 := by intro he; rw [he,zero_mul] at hz; exact zero_ne_one hz
  have hg : g (negPower KernelField 1) = (1+x)⁻¹ := by
    apply mul_left_cancel₀ ht
    rw [hz,mul_inv_cancel₀ ht]
  have hn := sigmaPullback_eval₂ (g.comp f) d p hp x ht
  apply seriesToField_injective
  rw [map_mul, map_pow, map_add, map_one, polynomialSeries_evalXY, substitutedSeries_evalXY]
  rw [hom_evalXY, hom_evalXY]
  simp only [evalXY_inX, map_neg]
  change (sigmaPullback d p).eval₂ (g.comp f) x =
    (1+x)^d*p.eval₂ (g.comp f) (-g (negPower KernelField 1))
  rw [hg]
  simpa only [div_eq_mul_inv, neg_mul, one_mul] using hn

theorem polynomialSeries_inX_coeff (p : ℚ[X]) (i : ℕ) :
    PowerSeries.coeff KernelField i (polynomialSeries (inX p)) = RatFunc.C (p.coeff i) := by
  rw [polynomialSeries_coeff]
  simp only [inX, Polynomial.coeff_map, coeffToField, RatFunc.algebraMap_C]

/-- 任意有限有理系数向量的 (6.4) 接口在 Q(y) 中忠实表示。 -/
theorem G_vector_series {q : ℕ} (p : ℚ[X]) (hp : p.natDegree < q) (i : Fin q) :
    PowerSeries.coeff KernelField i.val (negPower KernelField 1*substitutedSeries (inX p)) =
      RatFunc.C ((G q *ᵥ fun j => p.coeff j.val) i) := by
  rw [substitutedSeries_coeff (inX p) (by simpa using hp)]
  simp only [inX, Polynomial.coeff_map, map_sum, map_mul, Matrix.mulVec, dotProduct, G,
    coeffToField, RatFunc.algebraMap_C]

end CP.Kernel

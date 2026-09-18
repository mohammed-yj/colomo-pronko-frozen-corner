import CP.Kernel.Theta
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! 以外层变量表示 x，内层变量表示 y；各系数均属于 ℚ。 -/
namespace CP.Kernel
open Polynomial

abbrev Bivariate := Polynomial (Polynomial ℚ)

noncomputable def inX (p : ℚ[X]) : Bivariate := p.map Polynomial.C
noncomputable def inY (p : ℚ[X]) : Bivariate := Polynomial.C p
noncomputable def xx : Bivariate := Polynomial.X
noncomputable def yy : Bivariate := Polynomial.C Polynomial.X

noncomputable def denominator : Bivariate :=
  (yy-xx)*(1+xx+xx*yy)*(1+yy+xx*yy)

/-- 规范 (6.11) 的 F 的分子，标量分母 b² 已在 ℚ 内处理。 -/
noncomputable def fNumerator (N : ℕ) : Bivariate :=
  -Polynomial.C (Polynomial.C (epsilon N / b (N+1)^2)) *
    (inX ((u N).comp theta)*inY (v N) + inX ((v N).comp theta)*inY (u N)) *
    (inX ((u N).comp theta)*inY (vStar N) -
      inX ((v N).comp theta)*inY (uStar N))

/-- P = F + y^(2N)/(x-y) 通分后的实际分子。 -/
noncomputable def pNumerator (N : ℕ) : Bivariate :=
  fNumerator N - yy^(2*N)*(1+xx+xx*yy)*(1+yy+xx*yy)

/-- 规范 (4.12) 中真实 C 核的通分分子。 -/
noncomputable def cNumerator (N : ℕ) : Bivariate :=
  Polynomial.C (Polynomial.C ((b (N+1)^2)⁻¹)) *
    (inX (u N)*inY (v N)-inY (u N)*inX (v N)) *
    (inX (uStar N)*inY (vStar N)-inY (uStar N)*inX (vStar N)) -
    xx^(2*N)*(yy-xx)*(1+xx+xx*yy) +
    yy^(2*N)*(yy-xx)*(1+yy+xx*yy)

/-- 此处“互素”先在系数分式域中处理；回到多项式环使用本原性。 -/
theorem denominator_primitive : denominator.IsPrimitive := by
  have h0 : (yy-xx).IsPrimitive := by
    intro r hr
    have hd := ((Polynomial.C_dvd_iff_dvd_coeff _ _).mp hr) 1
    have hd' : r ∣ (-1 : ℚ[X]) := by simpa [xx, yy] using hd
    exact isUnit_of_dvd_one (by simpa using hd')
  have h1 : (1+xx+xx*yy).IsPrimitive := by
    intro r hr
    have hd := ((Polynomial.C_dvd_iff_dvd_coeff _ _).mp hr) 0
    exact isUnit_of_dvd_one (by simpa [xx, yy] using hd)
  have h2 : (1+yy+xx*yy).IsPrimitive := by
    intro r hr
    have hd0 := ((Polynomial.C_dvd_iff_dvd_coeff _ _).mp hr) 0
    have hd1 := ((Polynomial.C_dvd_iff_dvd_coeff _ _).mp hr) 1
    have hc0 : r ∣ (1+X : ℚ[X]) := by simpa [xx, yy] using hd0
    have hc1 : r ∣ (X : ℚ[X]) := by simpa [xx, yy, Polynomial.coeff_one] using hd1
    exact isUnit_of_dvd_one (by simpa using dvd_sub hc0 hc1)
  exact (h0.mul h1).mul h2

/-- 本项目需要的 Gauss 引理版本：被除式不必本原。 -/
theorem primitive_dvd_of_fraction_dvd {p q : Bivariate} (hp : p.IsPrimitive)
    (hd : p.map (algebraMap ℚ[X] (RatFunc ℚ)) ∣
      q.map (algebraMap ℚ[X] (RatFunc ℚ))) : p ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  have hc : algebraMap ℚ[X] (RatFunc ℚ) q.content ≠ 0 :=
    RatFunc.algebraMap_ne_zero (fun he => hq (Polynomial.content_eq_zero_iff.mp he))
  have hd' : p.map (algebraMap ℚ[X] (RatFunc ℚ)) ∣
      q.primPart.map (algebraMap ℚ[X] (RatFunc ℚ)) := by
    obtain ⟨r, hr⟩ := hd
    have he := q.eq_C_content_mul_primPart
    have hm := congrArg (Polynomial.map (algebraMap ℚ[X] (RatFunc ℚ))) he
    rw [Polynomial.map_mul, Polynomial.map_C] at hm
    refine ⟨C ((algebraMap ℚ[X] (RatFunc ℚ) q.content)⁻¹)*r, ?_⟩
    calc
      _ = C ((algebraMap ℚ[X] (RatFunc ℚ) q.content)⁻¹)*
          (C (algebraMap ℚ[X] (RatFunc ℚ) q.content)*
            q.primPart.map (algebraMap ℚ[X] (RatFunc ℚ))) := by
        rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, one_mul]
      _ = _ := by rw [← hm, hr]; ring
  exact (hp.dvd_of_fraction_map_dvd_fraction_map
    q.isPrimitive_primPart hd').trans q.primPart_dvd

@[simp] theorem eval_inX (p a : ℚ[X]) : (inX p).eval a = p.comp a := by
  rw [inX, Polynomial.eval_map]
  rfl

@[simp] theorem eval_inY (p a : ℚ[X]) : (inY p).eval a = p := by
  simp [inY]

theorem pNumerator_diagonal {N : ℕ} (hN : 1 ≤ N) :
    (pNumerator N).eval X = 0 := by
  have hb : b (N+1) ≠ 0 := (b_pos _ (by omega)).ne'
  have he : epsilon N / b (N+1)^2 * epsilon N * b (N+1) * b (N+1) = 1 := by
    have hs := epsilon_sq N
    field_simp [hb]
    linear_combination b (N+1)^2*hs
  have hc : C (epsilon N / b (N+1)^2)*C (epsilon N)*C (b (N+1))*C (b (N+1)) =
      (1 : ℚ[X]) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_mul, he, Polynomial.C_1]
  simp only [pNumerator, fNumerator, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, eval_inX, eval_inY, Polynomial.comp_X]
  rw [theta_pair hN, theta_star_pair hN]
  simp only [xx, yy, Polynomial.eval_X, Polynomial.eval_C]
  linear_combination X^(2*N)*(X^2+X+1)^2*hc

theorem diagonal_factor_dvd {N : ℕ} (hN : 1 ≤ N) :
    (yy-xx) ∣ pNumerator N := by
  have hd : (xx-yy) ∣ pNumerator N :=
    Polynomial.dvd_iff_isRoot.mpr (pNumerator_diagonal hN)
  have hn : -(xx-yy) ∣ pNumerator N := neg_dvd.mpr hd
  simpa only [neg_sub] using hn

end CP.Kernel

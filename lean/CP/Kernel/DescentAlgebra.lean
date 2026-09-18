import CP.Kernel.CReflection

set_option maxHeartbeats 2000000

namespace CP.Kernel
open Polynomial

noncomputable def thetaStarAlternant (N : ℕ) : Bivariate :=
  inX ((u N).comp theta)*inY (vStar N)-inX ((v N).comp theta)*inY (uStar N)

/-- (6.14) 余项的分子，完全有限多项式。 -/
noncomputable def descentRemainder (N : ℕ) : Bivariate :=
  C (C ((b (N+1)^2)⁻¹))*alternant N*thetaStarAlternant N

section FieldAlgebra
variable {F : Type*} [Field F] (f : ℚ →+* F)

theorem denominator_sigma (x y : F) (ht : 1+x ≠ 0) :
    (1+x)^3*evalXY f (-1/(1+x)) y denominator = -evalXY f x y denominator := by
  simp only [denominator, map_mul, map_add, map_sub, map_one, evalXY_xx, evalXY_yy]
  field_simp
  ring

theorem cNumerator_sigma {N : ℕ} (hN : 1 ≤ N) (x y : F) (ht : 1+x ≠ 0) :
    -(1+x)^(2*N+2)*evalXY f (-1/(1+x)) y (cNumerator N) =
      (1+x)^(2*N)*evalXY f x y (pNumerator N) +
      x^(2*N)*evalXY f x y (descentRemainder N) - (y-x)*(1+y+x*y) := by
  let U := (u N).eval₂ f x
  let V := (v N).eval₂ f x
  let Us := (uStar N).eval₂ f x
  let Vs := (vStar N).eval₂ f x
  let A := ((u N).comp theta).eval₂ f x
  let B := ((v N).comp theta).eval₂ f x
  let uy := (u N).eval₂ f y
  let vy := (v N).eval₂ f y
  let usy := (uStar N).eval₂ f y
  let vsy := (vStar N).eval₂ f y
  let eb := f (b (N+1))
  let es := f (epsilon N)
  have hb : eb ≠ 0 := by
    simpa only [map_zero] using f.injective.ne (b_pos (N+1) (by omega)).ne'
  have hes : es*es = 1 := by
    simpa only [map_mul, map_one] using congrArg f (epsilon_sq N)
  have hu := sigma_u_eval₂ f N x ht
  have hv := sigma_v_eval₂ f hN x ht
  have hus := sigma_uStar_eval₂ f N x ht
  have hvs := sigma_vStar_eval₂ f hN x ht
  have ha : A = (u N).eval₂ f (-1-x) := by simp [A, theta, Polynomial.eval₂_comp]
  have hh : B = (v N).eval₂ f (-1-x) := by simp [B, theta, Polynomial.eval₂_comp]
  rw [← ha] at hus
  rw [← hh] at hvs
  have hd : (1+x)^(N+1) ≠ 0 := pow_ne_zero _ ht
  have hu' : (u N).eval₂ f (-1/(1+x)) = -Us/(1+x)^(N+1) :=
    (eq_div_iff hd).mpr (by simpa only [mul_comm] using hu)
  have hv' : (v N).eval₂ f (-1/(1+x)) = Vs/(1+x)^(N+1) :=
    (eq_div_iff hd).mpr (by simpa only [mul_comm] using hv)
  have hus' : (uStar N).eval₂ f (-1/(1+x)) = (es*A)/(1+x)^(N+1) :=
    (eq_div_iff hd).mpr (by simpa only [mul_comm] using hus)
  have hvs' : (vStar N).eval₂ f (-1/(1+x)) = (es*B)/(1+x)^(N+1) :=
    (eq_div_iff hd).mpr (by simpa only [mul_comm] using hvs)
  have heU := congrArg (Polynomial.eval₂ f x) (uStar_theta N)
  have heV := congrArg (Polynomial.eval₂ f x) (vStar_theta hN)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_one,
    Polynomial.eval₂_X, Polynomial.eval₂_neg] at heU heV
  change Us = es*x^(2*N)*U-(1+x)^(2*N)*A at heU
  change Vs = -es*x^(2*N)*V-(1+x)^(2*N)*B at heV
  let w := (u N).eval₂ f (-1/(1+x))*vy-uy*(v N).eval₂ f (-1/(1+x))
  let ws := (uStar N).eval₂ f (-1/(1+x))*vsy-usy*(vStar N).eval₂ f (-1/(1+x))
  have hw : (1+x)^(N+1)*w = -Us*vy-uy*Vs := by
    dsimp only [w]
    linear_combination vy*hu-uy*hv
  have hws : (1+x)^(N+1)*ws = es*(A*vsy-B*usy) := by
    dsimp only [ws]
    linear_combination vsy*hus-usy*hvs
  have hprod : (1+x)^(2*N+2)*(w*ws) = -es*(Us*vy+uy*Vs)*(A*vsy-B*usy) := by
    calc
      _ = ((1+x)^(N+1)*w)*((1+x)^(N+1)*ws) := by
        rw [show 2*N+2 = (N+1)+(N+1) by omega, pow_add]; ring
      _ = _ := by rw [hw,hws]; ring
  have hp : (-1:F)^(2*N) = 1 := by rw [pow_mul]; norm_num
  have htail1 : (1+x)^(2*N+2)*(-1/(1+x))^(2*N)*
      (y-(-1/(1+x)))*(1+(-1/(1+x))+(-1/(1+x))*y) = (x-y)*(1+y+x*y) := by
    rw [div_pow, hp, pow_add]
    have hc : (1+x)^(2*N)*(1+x)^2*(1/(1+x)^(2*N)) = (1+x)^2 := by
      field_simp
    rw [hc]
    field_simp
    ring
  have htail2 : (1+x)^(2*N+2)*y^(2*N)*
      (y-(-1/(1+x)))*(1+y+(-1/(1+x))*y) =
      (1+x)^(2*N)*y^(2*N)*(1+x+x*y)*(1+y+x*y) := by
    have ht2 : (1+x)^2*(y-(-1/(1+x)))*(1+y+(-1/(1+x))*y) =
        (1+x+x*y)*(1+y+x*y) := by field_simp; ring
    rw [pow_add]
    linear_combination (1+x)^(2*N)*y^(2*N)*ht2
  simp only [cNumerator, pNumerator, fNumerator, descentRemainder, alternant,
    thetaStarAlternant, map_mul, map_add, map_sub, map_neg, map_pow, map_one,
    evalXY_inX, evalXY_inY, evalXY_xx, evalXY_yy, evalXY_constant, map_div₀, map_inv₀]
  change -(1+x)^(2*N+2)*((eb^2)⁻¹*w*ws -
    (-1/(1+x))^(2*N)*(y-(-1/(1+x)))*(1+(-1/(1+x))+(-1/(1+x))*y) +
    y^(2*N)*(y-(-1/(1+x)))*(1+y+(-1/(1+x))*y)) =
    (1+x)^(2*N)*(-(es/eb^2)*(A*vy+B*uy)*(A*vsy-B*usy)-y^(2*N)*(1+x+x*y)*(1+y+x*y))+
    x^(2*N)*((eb^2)⁻¹*(U*vy-V*uy)*(A*vsy-B*usy))-(y-x)*(1+y+x*y)
  rw [heU, heV] at hprod
  simp only [div_eq_mul_inv]
  linear_combination -(eb^2)⁻¹*hprod + htail1 - htail2 +
    (eb^2)⁻¹*x^(2*N)*(U*vy-V*uy)*(A*vsy-B*usy)*hes


/-- F4 的清分母版本。这里尚未使用任何幂级数或截断交换。 -/
theorem cKernel_sigma_cleared {N : ℕ} (hN : 1 ≤ N) (x y : F) (ht : 1+x ≠ 0) :
    (1+x)^(2*N)*evalXY f x y denominator *
      (evalXY f (-1/(1+x)) y (cKernel N)/(1+x)-evalXY f x y (pKernel N)) +
      (y-x)*(1+y+x*y) = x^(2*N)*evalXY f x y (descentRemainder N) := by
  have hd := denominator_sigma f x y ht
  have hc := congrArg (evalXY f (-1/(1+x)) y) (denominator_mul_cKernel hN)
  have hp := congrArg (evalXY f x y) (denominator_mul_pKernel hN)
  simp only [map_mul] at hc hp
  have hn := cNumerator_sigma f hN x y ht
  rw [← hc, ← hp] at hn
  have he : -(1+x)^(2*N+2)*
      (evalXY f (-1/(1+x)) y denominator*evalXY f (-1/(1+x)) y (cKernel N)) =
      (1+x)^(2*N)*evalXY f x y denominator*
      (evalXY f (-1/(1+x)) y (cKernel N)/(1+x)) := by
    have hd' : evalXY f x y denominator = -(1+x)^3*evalXY f (-1/(1+x)) y denominator := by
      linear_combination hd
    rw [hd', pow_add]
    field_simp
    ring
  rw [he] at hn
  linear_combination hn

end FieldAlgebra
end CP.Kernel

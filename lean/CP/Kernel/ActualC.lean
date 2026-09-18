import CP.Kernel.ReflectionIdentity
import CP.BinomialMatrices.KernelTruncation

namespace CP.Kernel
open Polynomial

noncomputable def evalXY {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) :
    Bivariate →+* F := Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f y) x

@[simp] theorem evalXY_inX {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) (p : ℚ[X]) :
    evalXY f x y (inX p) = p.eval₂ f x := by
  change (p.map Polynomial.C).eval₂ (Polynomial.eval₂RingHom f y) x = _
  rw [Polynomial.eval₂_map]
  congr 1
  ext a
  simp

@[simp] theorem evalXY_inY {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) (p : ℚ[X]) :
    evalXY f x y (inY p) = p.eval₂ f y := by
  simp [evalXY, inY]

@[simp] theorem evalXY_xx {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) :
    evalXY f x y xx = x := by simp [evalXY, xx]
@[simp] theorem evalXY_yy {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) :
    evalXY f x y yy = y := by simp [evalXY, yy]
@[simp] theorem evalXY_constant {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) (a : ℚ) :
    evalXY f x y (C (C a)) = f a := by simp [evalXY]

theorem evalXY_swap {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) (p : Bivariate) :
    evalXY f x y (swapXY p) = evalXY f y x p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    have ha : swapXY (C a) = inX a := by simpa only [inY] using swap_inY a
    have hx : swapXY (X : Bivariate) = yy := swap_xx
    simp only [map_mul, map_pow, ha, hx, evalXY_inX, evalXY_yy]
    change a.eval₂ f x * y^n = _
    simp [evalXY]

theorem cNumerator_swap (N : ℕ) : swapXY (cNumerator N) = cNumerator N := by
  simp only [cNumerator, map_add, map_sub, map_mul, map_pow,
    map_one, swap_inX, swap_inY, swap_xx, swap_yy, swap_constant]
  ring

theorem cNumerator_eval_swap {F : Type*} [CommRing F] (f : ℚ →+* F) (x y : F) (N : ℕ) :
    evalXY f x y (cNumerator N) = evalXY f y x (cNumerator N) := by
  rw [← cNumerator_swap N, evalXY_swap, cNumerator_swap]

theorem cNumerator_diagonal {F : Type*} [CommRing F] (f : ℚ →+* F) (y : F) (N : ℕ) :
    evalXY f y y (cNumerator N) = 0 := by
  simp only [cNumerator, map_add, map_sub, map_mul, map_pow,
    map_one, evalXY_inX, evalXY_inY, evalXY_xx, evalXY_yy, evalXY_constant]
  ring

/-- 从实际 F2 恒等式得到真实 C 核在第一个成对除子上的消去。 -/
theorem cNumerator_first_root {F : Type*} [Field F] (f : ℚ →+* F)
    {N : ℕ} (hN : 1 ≤ N) (y : F) (ht : 1+y ≠ 0) :
    evalXY f (-1/(1+y)) y (cNumerator N) = 0 := by
  let U := (u N).eval₂ f y
  let V := (v N).eval₂ f y
  let Us := (uStar N).eval₂ f y
  let Vs := (vStar N).eval₂ f y
  let A := ((u N).comp theta).eval₂ f y
  let B := ((v N).comp theta).eval₂ f y
  let eb := f (b (N+1))
  let es := f (epsilon N)
  have hb : eb ≠ 0 := by
    simpa only [map_zero] using f.injective.ne (b_pos (N+1) (by omega)).ne'
  have hes : es*es = 1 := by
    have he := congrArg f (epsilon_sq N)
    simpa only [map_mul, map_one] using he
  have hpair := congrArg (Polynomial.eval₂ f y) (uvStar_pair hN)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_one, Polynomial.eval₂_X] at hpair
  change U*Vs+Us*V = eb*(1+y)^(2*N)*(y^2+y+1) at hpair
  have hstar := congrArg (Polynomial.eval₂ f y) (theta_star_pair hN)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_one, Polynomial.eval₂_X,
    Polynomial.eval₂_add] at hstar
  change A*Vs-B*Us = es*eb*y^(2*N)*(y^2+y+1) at hstar
  have hu := sigma_u_eval₂ f N y ht
  have hv := sigma_v_eval₂ f hN y ht
  have hus := sigma_uStar_eval₂ f N y ht
  have hvs := sigma_vStar_eval₂ f hN y ht
  have ha : A = (u N).eval₂ f (-1-y) := by simp [A, theta, Polynomial.eval₂_comp]
  have hh : B = (v N).eval₂ f (-1-y) := by simp [B, theta, Polynomial.eval₂_comp]
  rw [← ha] at hus
  rw [← hh] at hvs
  have hw : (1+y)^(N+1)*
      ((u N).eval₂ f (-1/(1+y))*V-U*(v N).eval₂ f (-1/(1+y))) =
        -eb*(1+y)^(2*N)*(y^2+y+1) := by
    linear_combination V*hu-U*hv-hpair
  have hws : (1+y)^(N+1)*
      ((uStar N).eval₂ f (-1/(1+y))*Vs-Us*(vStar N).eval₂ f (-1/(1+y))) =
        eb*y^(2*N)*(y^2+y+1) := by
    linear_combination Vs*hus-Us*hvs+es*hstar+eb*y^(2*N)*(y^2+y+1)*hes
  have hd : (1+y)^(N+1) ≠ 0 := pow_ne_zero _ ht
  have hw' :
      (u N).eval₂ f (-1/(1+y))*V-U*(v N).eval₂ f (-1/(1+y)) =
        (-eb*(1+y)^(2*N)*(y^2+y+1))/(1+y)^(N+1) :=
    (eq_div_iff hd).mpr (by simpa only [mul_comm] using hw)
  have hws' :
      (uStar N).eval₂ f (-1/(1+y))*Vs-Us*(vStar N).eval₂ f (-1/(1+y)) =
        (eb*y^(2*N)*(y^2+y+1))/(1+y)^(N+1) :=
    (eq_div_iff hd).mpr (by simpa only [mul_comm] using hws)
  have hl : 1+(-1/(1+y))+(-1/(1+y))*y = 0 := by field_simp
  simp only [cNumerator, map_add, map_sub, map_mul, map_pow, map_one,
    evalXY_inX, evalXY_inY, evalXY_xx, evalXY_yy, evalXY_constant]
  change f ((b (N+1)^2)⁻¹)*
    ((u N).eval₂ f (-1/(1+y))*V-U*(v N).eval₂ f (-1/(1+y)))*
    ((uStar N).eval₂ f (-1/(1+y))*Vs-Us*(vStar N).eval₂ f (-1/(1+y))) -
    (-1/(1+y))^(2*N)*(y-(-1/(1+y)))*(1+(-1/(1+y))+(-1/(1+y))*y) +
    y^(2*N)*(y-(-1/(1+y)))*(1+y+(-1/(1+y))*y) = 0
  rw [hw', hws', hl]
  simp only [mul_zero, sub_zero, map_inv₀, map_pow]
  change (eb^2)⁻¹ * _ * _ + _ = 0
  rw [show 2*N = N+N by omega]
  simp only [pow_add, pow_succ]
  field_simp [ht, hb, pow_ne_zero N ht]
  ring


theorem cNumerator_second_root {F : Type*} [Field F] (f : ℚ →+* F)
    {N : ℕ} (hN : 1 ≤ N) (y : F) (hy : y ≠ 0) :
    evalXY f (-(1+y)/y) y (cNumerator N) = 0 := by
  let x := -(1+y)/y
  have hx : 1+x ≠ 0 := by
    have he : 1+x = -1/y := by dsimp [x]; field_simp
    rw [he]
    exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hy
  have hs : -1/(1+x) = y := by
    dsimp [x]
    field_simp
  have hr := cNumerator_first_root f hN x hx
  rw [hs, cNumerator_eval_swap] at hr
  exact hr

theorem beval_eq_evalXY (a : KernelField) (p : Bivariate) :
    beval a p = evalXY RatFunc.C a RatFunc.X p := by
  have he : coeffToField = Polynomial.eval₂RingHom RatFunc.C RatFunc.X := by
    apply RingHom.ext
    intro q
    exact coeffToField_eq_eval q
  simp only [beval, evalXY, he]

/-- 在 Q(y) 中的三个互异根，经本原性下降回 Q[x,y]。 -/
theorem denominator_dvd_of_roots (p : Bivariate)
    (hzero : beval RatFunc.X p = 0)
    (hfirst : beval (-1/(1+RatFunc.X)) p = 0)
    (hsecond : beval (-(1+RatFunc.X)/RatFunc.X) p = 0) :
    denominator ∣ p := by
  apply primitive_dvd_of_fraction_dvd denominator_primitive
  let pf := p.map coeffToField
  have h0 : (X-C RatFunc.X : Polynomial KernelField) ∣ pf := by
    apply Polynomial.dvd_iff_isRoot.mpr
    change pf.eval RatFunc.X = 0
    dsimp only [pf]
    rw [Polynomial.eval_map]
    exact hzero
  have h1 : (X-C (-1/(1+RatFunc.X)) : Polynomial KernelField) ∣ pf := by
    apply Polynomial.dvd_iff_isRoot.mpr
    change pf.eval (-1/(1+RatFunc.X)) = 0
    dsimp only [pf]
    rw [Polynomial.eval_map]
    exact hfirst
  have h2 : (X-C (-(1+RatFunc.X)/RatFunc.X) : Polynomial KernelField) ∣ pf := by
    apply Polynomial.dvd_iff_isRoot.mpr
    change pf.eval (-(1+RatFunc.X)/RatFunc.X) = 0
    dsimp only [pf]
    rw [Polynomial.eval_map]
    exact hsecond
  obtain ⟨hd01, hd02, hd12⟩ := field_three_roots_distinct
  have hc01 := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hd01).isUnit
  have hc02 := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hd02).isUnit
  have hc12 := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hd12).isUnit
  obtain ⟨r, hr⟩ := (hc02.mul_left hc12).mul_dvd (hc01.mul_dvd h0 h1) h2
  let c : KernelField := -(1+RatFunc.X)*RatFunc.X
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr field_one_add_ne_zero) RatFunc.X_ne_zero
  change denominator.map coeffToField ∣ pf
  refine ⟨C c⁻¹*r, ?_⟩
  rw [denominator_field_factor]
  change pf = C c * _ * (C c⁻¹*r)
  rw [hr]
  have hu : (C c : Polynomial KernelField)*C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  linear_combination -((X-C RatFunc.X)*(X-C (-1/(1+RatFunc.X)))*
    (X-C (-(1+RatFunc.X)/RatFunc.X)))*r*hu


theorem denominator_dvd_cNumerator {N : ℕ} (hN : 1 ≤ N) :
    denominator ∣ cNumerator N := by
  apply denominator_dvd_of_roots
  · rw [beval_eq_evalXY]
    exact cNumerator_diagonal RatFunc.C RatFunc.X N
  · rw [beval_eq_evalXY]
    exact cNumerator_first_root RatFunc.C hN RatFunc.X field_one_add_ne_zero
  · rw [beval_eq_evalXY]
    exact cNumerator_second_root RatFunc.C hN RatFunc.X RatFunc.X_ne_zero

/-- 真实核 (4.12) 的实际多项式商；定义只使用原分子及其整除证明。 -/
noncomputable def cKernel (N : ℕ) : Bivariate :=
  if hN : 1 ≤ N then Classical.choose (denominator_dvd_cNumerator hN) else 0

theorem denominator_mul_cKernel {N : ℕ} (hN : 1 ≤ N) :
    denominator*cKernel N = cNumerator N := by
  unfold cKernel
  rw [dif_pos hN]
  exact (Classical.choose_spec (denominator_dvd_cNumerator hN)).symm

theorem cKernel_swap {N : ℕ} (hN : 1 ≤ N) : swapXY (cKernel N) = -cKernel N := by
  apply mul_left_cancel₀ denominator_primitive.ne_zero
  have he := congrArg swapXY (denominator_mul_cKernel hN)
  rw [map_mul, swap_denominator, cNumerator_swap] at he
  linear_combination -he + denominator_mul_cKernel hN

theorem cNumerator_degree {N : ℕ} (hN : 1 ≤ N) :
    (cNumerator N).natDegree ≤ 2*N+2 := by
  have hu := u_degree N
  have hv := (v_degree hN).trans (Nat.le_succ _)
  have hus : (uStar N).natDegree ≤ N+1 := reflect_degree _ _ hu
  have hvs : (vStar N).natDegree ≤ N+1 := reflect_degree _ _ hv
  have h1 := bracket_sub_degree (u N) (v N) (v N) (u N) (N+1) hu hv
  have h2 := bracket_sub_degree (uStar N) (vStar N) (vStar N) (uStar N) (N+1) hus hvs
  have hfirst : (C (C ((b (N+1)^2)⁻¹)) *
      (inX (u N)*inY (v N)-inY (u N)*inX (v N)) *
      (inX (uStar N)*inY (vStar N)-inY (uStar N)*inX (vStar N))).natDegree ≤ 2*N+2 := by
    have he1 : inX (u N)*inY (v N)-inY (u N)*inX (v N) =
        inX (u N)*inY (v N)-inX (v N)*inY (u N) := by ring
    have he2 : inX (uStar N)*inY (vStar N)-inY (uStar N)*inX (vStar N) =
        inX (uStar N)*inY (vStar N)-inX (vStar N)*inY (uStar N) := by ring
    rw [he1, he2]
    have h0 : (C (C ((b (N+1)^2)⁻¹)) : Bivariate).natDegree ≤ 0 := by simp
    exact (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le h0 h1) h2).trans (by omega)
  have hx : (xx^(2*N)).natDegree ≤ 2*N := by simp [xx]
  have hy : (yy^(2*N)).natDegree ≤ 0 := by simp [yy]
  have hd : (yy-xx).natDegree ≤ 1 := by unfold xx yy; compute_degree <;> norm_num
  have ht1 := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le hx hd) pair_factor_degrees.1
  have ht2 := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le hy hd) pair_factor_degrees.2
  unfold cNumerator
  exact Polynomial.natDegree_add_le_of_degree_le
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hfirst (ht1.trans (by omega))))
    (ht2.trans (by omega))

theorem cKernel_degree {N : ℕ} (hN : 1 ≤ N) :
    (cKernel N).natDegree ≤ 2*N-1 := by
  by_cases hc : cKernel N = 0
  · simp [hc]
  have he := Polynomial.natDegree_mul denominator_primitive.ne_zero hc
  rw [denominator_mul_cKernel hN, denominator_degree] at he
  have hb := cNumerator_degree hN
  omega

theorem swap_cKernel_degree {N : ℕ} (hN : 1 ≤ N) :
    (swapXY (cKernel N)).natDegree ≤ 2*N-1 := by
  rw [cKernel_swap hN, Polynomial.natDegree_neg]
  exact cKernel_degree hN

/-- C^{(N)} 是真实核的有限系数矩阵，不涉及 G 或目标矩阵等式。 -/
noncomputable def cMatrix (N : ℕ) : Matrix (Fin (2*N)) (Fin (2*N)) ℚ :=
  fun i j => (cKernel N).coeff i.val |>.coeff j.val

theorem cMatrix_skew {N : ℕ} (hN : 1 ≤ N) : (cMatrix N).transpose = -cMatrix N := by
  ext i j
  have he := congrArg (fun p : Bivariate => (p.coeff i.val).coeff j.val) (cKernel_swap hN)
  simpa only [swap_coeff, Polynomial.coeff_neg] using he

end CP.Kernel

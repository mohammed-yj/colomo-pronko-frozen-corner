import CP.Polynomial.Adjacent
import Mathlib.Algebra.Polynomial.Roots

namespace CP.Kernel
open Polynomial

noncomputable def u (N : ℕ) : ℚ[X] := X * (h (N+1)).comp (1+X)
noncomputable def v (N : ℕ) : ℚ[X] := (1+X) * (h N).comp (1+X)
noncomputable def uStar (N : ℕ) : ℚ[X] := (u N).reflect (N+1)
noncomputable def vStar (N : ℕ) : ℚ[X] := (v N).reflect (N+1)
def epsilon (N : ℕ) : ℚ := (-1)^(N+1)
noncomputable def theta : ℚ[X] := -1-X
def sigma (x : ℚ) : ℚ := -1/(1+x)

theorem polynomial_eq_of_eval_off (p q : ℚ[X])
    (he : ∀ x : ℚ, x ≠ 0 → x ≠ -1 → p.eval x = q.eval x) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.infinite_univ : (Set.univ : Set ℚ).Infinite).diff
    (Set.toFinite ({0,-1} : Set ℚ))).mono
  intro x hx
  have hx' : x ≠ 0 ∧ x ≠ -1 := by simpa using hx.2
  exact he x hx'.1 hx'.2

theorem reflect_eval (p : ℚ[X]) (d : ℕ) (hp : p.natDegree ≤ d)
    (x : ℚ) (hx : x ≠ 0) : (p.reflect d).eval x = x^d * p.eval x⁻¹ := by
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have he := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℚ) x⁻¹ d p hp
  simp only [invOf_eq_inv, inv_inv, inv_pow] at he
  change (p.reflect d).eval x * (x^d)⁻¹ = p.eval x⁻¹ at he
  have hh := congrArg (fun a : ℚ => a*x^d) he
  simpa [mul_assoc, pow_ne_zero d hx, mul_comm] using hh

theorem h_reciprocal (m : ℕ) (hm : 1 ≤ m) (x : ℚ) (hx : x ≠ 0) :
    x^(m-1) * (h m).eval x⁻¹ = (h m).eval x := by
  have hr := Fractional.reflect_h (m-1)
  rw [Nat.sub_add_cancel hm] at hr
  rw [← reflect_eval _ _ (by have := h_natDegree_lt m hm; omega) x hx, hr]

theorem one_add_X_degree : (1+X : ℚ[X]).natDegree = 1 := by
  compute_degree <;> norm_num

theorem u_degree (N : ℕ) : (u N).natDegree ≤ N+1 := by
  have hh := h_natDegree_lt (N+1) (by omega)
  have hc := Polynomial.natDegree_comp_le (p := h (N+1)) (q := (1+X : ℚ[X]))
  rw [one_add_X_degree, mul_one] at hc
  have ht := Polynomial.natDegree_mul_le (p := (X : ℚ[X]))
    (q := (h (N+1)).comp (1+X))
  simp only [Polynomial.natDegree_X] at ht
  unfold u
  omega

theorem v_degree {N : ℕ} (hN : 1 ≤ N) : (v N).natDegree ≤ N := by
  have hh := h_natDegree_lt N hN
  have hc := Polynomial.natDegree_comp_le (p := h N) (q := (1+X : ℚ[X]))
  rw [one_add_X_degree, mul_one] at hc
  have ht := Polynomial.natDegree_mul_le (p := (1+X : ℚ[X]))
    (q := (h N).comp (1+X))
  rw [one_add_X_degree] at ht
  unfold v
  omega

@[simp] theorem u_eval (N : ℕ) (x : ℚ) :
    (u N).eval x = x*(h (N+1)).eval (1+x) := by simp [u]
@[simp] theorem v_eval (N : ℕ) (x : ℚ) :
    (v N).eval x = (1+x)*(h N).eval (1+x) := by simp [v]

theorem uStar_eval (N : ℕ) (x : ℚ) (hx : x ≠ 0) :
    (uStar N).eval x = x^N*(h (N+1)).eval ((1+x)/x) := by
  rw [uStar, reflect_eval _ _ (u_degree N) x hx, u_eval]
  have ht : 1+x⁻¹ = (1+x)/x := by field_simp; ring
  rw [ht, pow_succ]
  field_simp
  <;> ring

theorem vStar_eval {N : ℕ} (hN : 1 ≤ N) (x : ℚ) (hx : x ≠ 0) :
    (vStar N).eval x = (1+x)*x^N*(h N).eval ((1+x)/x) := by
  rw [vStar, reflect_eval _ _ (by have := v_degree hN; omega) x hx, v_eval]
  have ht : 1+x⁻¹ = (1+x)/x := by field_simp; ring
  rw [ht, pow_succ]
  field_simp
  <;> ring

theorem homogeneous_h_identity (q : ℕ) (x : ℚ) (hx : x ≠ 0) :
    x^q*(h (q+1)).eval ((1+x)/x) =
      (-1)^(q+1)*x^(2*q+1)*(h (q+1)).eval (1+x) +
      (1+x)^(2*q+1)*(h (q+1)).eval (-x) := by
  have he := congrArg (Polynomial.eval (1+x)) (Fractional.fractional_cleared q)
  rw [Fractional.substPoly_eval _ _ (by intro he; apply hx; linarith : 1+x ≠ 1)] at he
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_comp] at he
  rw [show 1-(1+x) = -x by ring, show 1+x-1 = x by ring] at he
  rw [neg_pow x q, neg_pow x (2*q+1)] at he
  have hs : (-1:ℚ)^q*(-1)^q = 1 := by
    rw [← pow_add, show q+q = 2*q by omega, pow_mul]
    norm_num
  have ho : (-1:ℚ)^(2*q+1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [ho] at he
  have hh := congrArg (fun a : ℚ => (-1)^q*a) he
  have hl : (-1:ℚ)^q*((-1)^q*x^q*(h (q+1)).eval ((1+x)/x)) =
      x^q*(h (q+1)).eval ((1+x)/x) := by rw [← mul_assoc, ← mul_assoc, hs]; ring
  dsimp only at hh
  rw [hl] at hh
  rw [hh, pow_succ]
  linear_combination (1+x)^(2*q+1)*(h (q+1)).eval (-x)*hs

theorem uStar_theta (N : ℕ) :
    uStar N = C (epsilon N)*X^(2*N)*u N - (1+X)^(2*N)*(u N).comp theta := by
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  rw [uStar_eval N x hx]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_comp, theta, Polynomial.eval_neg, u_eval]
  rw [homogeneous_h_identity N x hx]
  simp only [epsilon, show 1+(-1-x) = -x by ring, pow_succ]
  ring

theorem vStar_theta {N : ℕ} (hN : 1 ≤ N) :
    vStar N = -C (epsilon N)*X^(2*N)*v N - (1+X)^(2*N)*(v N).comp theta := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  rw [vStar_eval (by omega) x hx]
  simp only [Nat.succ_eq_add_one, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_comp, theta, Polynomial.eval_neg, v_eval]
  have he := homogeneous_h_identity q x hx
  simp only [epsilon, show 1+(-1-x) = -x by ring,
    show 2*(q+1) = (2*q+1)+1 by omega, pow_succ]
  simp only [pow_succ] at he
  linear_combination (1+x)*x*he

theorem uvStar_pair {N : ℕ} (hN : 1 ≤ N) :
    u N*vStar N+uStar N*v N =
      C (b (N+1))*(1+X)^(2*N)*(X^2+X+1) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  have ht : 1+x ≠ 0 := by intro he; apply hx1; linarith
  have ht1 : 1+x ≠ 1 := by intro he; apply hx; linarith
  have hr : x/(1+x) ≠ 0 := div_ne_zero hx ht
  have h1 := h_reciprocal (q+2) (by omega) (x/(1+x)) hr
  have h2 := h_reciprocal (q+1) (by omega) (x/(1+x)) hr
  simp only [inv_div, show q+2-1 = q+1 by omega, Nat.add_sub_cancel] at h1 h2
  have he := Adjacent.adjacent_pair (m := q+2) (by omega) ht ht1
  simp only [rho, show 1+x-1 = x by ring,
    show q+2-1 = q+1 by omega, show q+2-2 = q by omega] at he
  rw [← h1, ← h2] at he
  simp only [Nat.succ_eq_add_one, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_X,
    u_eval, v_eval, uStar_eval _ _ hx, vStar_eval (N := q+1) (by omega) _ hx]
  simp only [div_pow, pow_succ] at he
  field_simp [ht, pow_ne_zero q ht] at he
  apply mul_left_cancel₀ (pow_ne_zero q ht)
  linear_combination he

/-- 固定次数的齐次 Möbius 代换；始终是有限多项式。 -/
noncomputable def sigmaPullback (d : ℕ) (p : ℚ[X]) : ℚ[X] :=
  C ((-1:ℚ)^d) * (p.reflect d).comp theta

theorem reflect_twice (p : ℚ[X]) (d : ℕ) : (p.reflect d).reflect d = p := by
  ext i
  simp only [Polynomial.coeff_reflect, Polynomial.revAt_invol]

theorem reflect_degree (p : ℚ[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    (p.reflect d).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hi]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hi)

theorem sigmaPullback_eval (d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d)
    (x : ℚ) (hx : x ≠ -1) :
    (sigmaPullback d p).eval x = (1+x)^d*p.eval (sigma x) := by
  have ht : -1-x ≠ 0 := by intro he; apply hx; linarith
  simp only [sigmaPullback, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, theta, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_X]
  rw [reflect_eval _ _ hp _ ht]
  have ht1 : 1+x ≠ 0 := by intro he; apply hx; linarith
  have hi : (-1-x)⁻¹ = sigma x := by unfold sigma; field_simp; ring
  rw [hi, ← mul_assoc, ← mul_pow, show (-1:ℚ)*(-1-x) = 1+x by ring]

theorem uStar_theta_parity (N : ℕ) :
    (uStar N).comp theta = C ((-1:ℚ)^N)*uStar N := by
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  have ht : 1+x ≠ 0 := by intro he; apply hx1; linarith
  have htheta : -1-x ≠ 0 := by intro he; apply hx1; linarith
  have hr := h_reciprocal (N+1) (by omega) (x/(1+x)) (div_ne_zero hx ht)
  simp only [Nat.add_sub_cancel, inv_div] at hr
  simp only [Polynomial.eval_comp, theta, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  rw [uStar_eval _ _ htheta, uStar_eval _ _ hx]
  have ha : (1+(-1-x))/(-1-x) = x/(1+x) := by field_simp; ring
  rw [ha, ← hr, ← mul_assoc, ← mul_pow,
    show (-1-x)*(x/(1+x)) = -x by field_simp; ring,
    neg_pow]
  ring

theorem vStar_theta_parity {N : ℕ} (hN : 1 ≤ N) :
    (vStar N).comp theta = C (epsilon N)*vStar N := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  have ht : 1+x ≠ 0 := by intro he; apply hx1; linarith
  have htheta : -1-x ≠ 0 := by intro he; apply hx1; linarith
  have hr := h_reciprocal (q+1) (by omega) (x/(1+x)) (div_ne_zero hx ht)
  simp only [Nat.add_sub_cancel, inv_div] at hr
  simp only [Polynomial.eval_comp, theta, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  rw [vStar_eval (by omega) _ htheta, vStar_eval (by omega) _ hx]
  have ha : (1+(-1-x))/(-1-x) = x/(1+x) := by field_simp; ring
  rw [ha, ← hr]
  simp only [Nat.succ_eq_add_one, epsilon, pow_succ]
  have hp : (-1-x)^q*(x/(1+x))^q = (-1:ℚ)^q*x^q := by
    rw [← mul_pow, show (-1-x)*(x/(1+x)) = -x by field_simp; ring, neg_pow]
  linear_combination (1+x)*x*hp*(h (q+1)).eval ((1+x)/x)

/-- (6.10) 第一式的有限多项式形式。 -/
theorem sigma_u (N : ℕ) : sigmaPullback (N+1) (u N) = -uStar N := by
  unfold sigmaPullback
  change C ((-1:ℚ)^(N+1))*(uStar N).comp theta = _
  rw [uStar_theta_parity, ← mul_assoc, ← Polynomial.C_mul]
  have hs : (-1:ℚ)^(N+1)*(-1)^N = -1 := by
    rw [← pow_add, show N+1+N = 2*N+1 by omega, pow_add, pow_mul]
    norm_num
  rw [hs]
  simp

/-- (6.10) 第二式的有限多项式形式。 -/
theorem sigma_v {N : ℕ} (hN : 1 ≤ N) :
    sigmaPullback (N+1) (v N) = vStar N := by
  unfold sigmaPullback
  change C ((-1:ℚ)^(N+1))*(vStar N).comp theta = _
  rw [vStar_theta_parity hN, ← mul_assoc, ← Polynomial.C_mul]
  have hs : (-1:ℚ)^(N+1)*epsilon N = 1 := by
    unfold epsilon
    rw [← pow_add, show N+1+(N+1) = 2*(N+1) by omega, pow_mul]
    norm_num
  rw [hs]
  simp

/-- (6.10) 第三式的有限多项式形式。 -/
theorem sigma_uStar (N : ℕ) :
    sigmaPullback (N+1) (uStar N) = C (epsilon N)*(u N).comp theta := by
  unfold sigmaPullback uStar
  rw [reflect_twice]
  rfl

/-- (6.10) 第四式的有限多项式形式。 -/
theorem sigma_vStar (N : ℕ) :
    sigmaPullback (N+1) (vStar N) = C (epsilon N)*(v N).comp theta := by
  unfold sigmaPullback vStar
  rw [reflect_twice]
  rfl

theorem sigma_u_eval (N : ℕ) (x : ℚ) (hx : x ≠ -1) :
    (u N).eval (sigma x) = -(uStar N).eval x / (1+x)^(N+1) := by
  have ht : 1+x ≠ 0 := by intro he; apply hx; linarith
  apply (eq_div_iff (pow_ne_zero _ ht)).mpr
  have he := congrArg (Polynomial.eval x) (sigma_u N)
  rw [sigmaPullback_eval _ _ (u_degree N) _ hx, Polynomial.eval_neg] at he
  simpa [mul_comm] using he

theorem sigma_v_eval {N : ℕ} (hN : 1 ≤ N) (x : ℚ) (hx : x ≠ -1) :
    (v N).eval (sigma x) = (vStar N).eval x / (1+x)^(N+1) := by
  have ht : 1+x ≠ 0 := by intro he; apply hx; linarith
  apply (eq_div_iff (pow_ne_zero _ ht)).mpr
  have he := congrArg (Polynomial.eval x) (sigma_v hN)
  rw [sigmaPullback_eval _ _ (by have := v_degree hN; omega) _ hx] at he
  simpa [mul_comm] using he

theorem sigma_uStar_eval (N : ℕ) (x : ℚ) (hx : x ≠ -1) :
    (uStar N).eval (sigma x) = epsilon N*(u N).eval (-1-x)/(1+x)^(N+1) := by
  have ht : 1+x ≠ 0 := by intro he; apply hx; linarith
  apply (eq_div_iff (pow_ne_zero _ ht)).mpr
  have he := congrArg (Polynomial.eval x) (sigma_uStar N)
  rw [sigmaPullback_eval (N+1) (uStar N) (by exact reflect_degree _ _ (u_degree N)) _ hx] at he
  simpa [theta, mul_comm] using he

theorem sigma_vStar_eval {N : ℕ} (hN : 1 ≤ N) (x : ℚ) (hx : x ≠ -1) :
    (vStar N).eval (sigma x) = epsilon N*(v N).eval (-1-x)/(1+x)^(N+1) := by
  have ht : 1+x ≠ 0 := by intro he; apply hx; linarith
  apply (eq_div_iff (pow_ne_zero _ ht)).mpr
  have he := congrArg (Polynomial.eval x) (sigma_vStar N)
  rw [sigmaPullback_eval (N+1) (vStar N) (by exact reflect_degree _ _ (by have := v_degree hN; omega)) _ hx] at he
  simpa [theta, mul_comm] using he

theorem one_add_X_ne_zero : (1+X : ℚ[X]) ≠ 0 := by
  intro he
  have hh := congrArg (Polynomial.eval (0:ℚ)) he
  norm_num at hh

/-- F3 对角消去所需的第一个实际括号值。 -/
theorem theta_pair {N : ℕ} (hN : 1 ≤ N) :
    (u N).comp theta*v N + (v N).comp theta*u N =
      -C (b (N+1))*(X^2+X+1) := by
  apply mul_left_cancel₀ (pow_ne_zero (2*N) one_add_X_ne_zero)
  have hu := uStar_theta N
  have hv := vStar_theta hN
  have he := uvStar_pair hN
  linear_combination v N*hu + u N*hv - he

/-- F3 对角消去所需的第二个实际括号值。 -/
theorem theta_star_pair {N : ℕ} (hN : 1 ≤ N) :
    (u N).comp theta*vStar N - (v N).comp theta*uStar N =
      C (epsilon N)*C (b (N+1))*X^(2*N)*(X^2+X+1) := by
  have hu := uStar_theta N
  have hv := vStar_theta hN
  have he := theta_pair hN
  linear_combination (u N).comp theta*hv - (v N).comp theta*hu -
    C (epsilon N)*X^(2*N)*he

end CP.Kernel

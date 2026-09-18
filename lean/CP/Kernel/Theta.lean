import CP.Kernel.Transport

namespace CP.Kernel
open Polynomial

theorem theta_comp_degree (p : ℚ[X]) : (p.comp theta).natDegree ≤ p.natDegree := by
  have ht : theta.natDegree = 1 := by unfold theta; compute_degree <;> norm_num [Polynomial.coeff_one]
  have hp := Polynomial.natDegree_comp_le (p := p) (q := theta)
  simpa only [ht, mul_one] using hp

theorem h_reciprocal_neg (m : ℕ) (hm : 1 ≤ m) (x : ℚ) (hx : x ≠ 0) :
    x^(m-1)*(h m).eval (-x⁻¹) = (-1)^(m-1)*(h m).eval (-x) := by
  have hr := h_reciprocal m hm (-x) (neg_ne_zero.mpr hx)
  rw [← neg_inv, neg_pow] at hr
  have hs : (-1:ℚ)^(m-1)*(-1)^(m-1) = 1 := by
    rw [← pow_add, show m-1+(m-1) = 2*(m-1) by omega, pow_mul]
    norm_num
  linear_combination (-1)^(m-1)*hr - x^(m-1)*(h m).eval (-x⁻¹)*hs

theorem theta_u_reflect (N : ℕ) :
    ((u N).comp theta).reflect (N+1) = -C (epsilon N)*(u N).comp theta := by
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  rw [reflect_eval _ _ ((theta_comp_degree _).trans (u_degree N)) _ hx]
  simp only [Polynomial.eval_comp, theta, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
    u_eval]
  have hr := h_reciprocal_neg (N+1) (by omega) x hx
  simp only [Nat.add_sub_cancel] at hr
  simp only [show 1+(-1-x⁻¹) = -x⁻¹ by ring,
    show 1+(-1-x) = -x by ring, epsilon, pow_succ]
  field_simp [hx]
  simp only [neg_div, one_div]
  linear_combination -x*(1+x)*hr

theorem theta_v_reflect {N : ℕ} (hN : 1 ≤ N) :
    ((v N).comp theta).reflect (N+1) = C (epsilon N)*(v N).comp theta := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  apply polynomial_eq_of_eval_off
  intro x hx hx1
  rw [reflect_eval _ _ ((theta_comp_degree _).trans ((v_degree (N := q.succ) (by omega)).trans (Nat.le_succ _))) _ hx]
  simp only [Polynomial.eval_comp, theta, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
    v_eval]
  have hr := h_reciprocal_neg (q+1) (by omega) x hx
  simp only [Nat.add_sub_cancel] at hr
  simp only [show 1+(-1-x⁻¹) = -x⁻¹ by ring,
    show 1+(-1-x) = -x by ring, Nat.succ_eq_add_one, epsilon, pow_succ]
  field_simp [hx]
  simp only [neg_div, one_div]
  linear_combination x^2*hr

theorem epsilon_sq (N : ℕ) : epsilon N*epsilon N = 1 := by
  unfold epsilon
  rw [← pow_add, show N+1+(N+1) = 2*(N+1) by omega, pow_mul]
  norm_num

theorem theta_involution (p : ℚ[X]) : (p.comp theta).comp theta = p := by
  rw [Polynomial.comp_assoc]
  have ht : theta.comp theta = (X : ℚ[X]) := by simp [theta] <;> ring
  rw [ht, Polynomial.comp_X]

theorem sigma_theta_u (N : ℕ) :
    sigmaPullback (N+1) ((u N).comp theta) = -u N := by
  unfold sigmaPullback
  rw [theta_u_reflect]
  simp only [neg_mul, Polynomial.neg_comp, Polynomial.mul_comp,
    Polynomial.C_comp, theta_involution]
  change C (epsilon N)*-(C (epsilon N)*u N) = _
  rw [mul_neg, ← mul_assoc, ← Polynomial.C_mul, epsilon_sq, Polynomial.C_1, one_mul]

theorem sigma_theta_v {N : ℕ} (hN : 1 ≤ N) :
    sigmaPullback (N+1) ((v N).comp theta) = v N := by
  unfold sigmaPullback
  rw [theta_v_reflect hN]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, theta_involution]
  change C (epsilon N)*(C (epsilon N)*v N) = _
  rw [← mul_assoc, ← Polynomial.C_mul, epsilon_sq, Polynomial.C_1, one_mul]

end CP.Kernel

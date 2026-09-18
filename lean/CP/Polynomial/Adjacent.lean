import CP.Polynomial.Recurrence

namespace CP.Adjacent
open Polynomial

noncomputable def g (m : ℕ) (z : ℚ) : ℚ := rho z ^ m * (h m).eval z
noncomputable def W (m : ℕ) (z : ℚ) : ℚ :=
  g m z*g (m-1) (rho z)-g (m-1) z*g m (rho z)
noncomputable def L (m : ℕ) (z : ℚ) : ℚ :=
  (h m).eval (rho z)*(h (m-1)).eval z+
    (z-1)^2/z*(h m).eval z*(h (m-1)).eval (rho z)

theorem recurrence_eval {m : ℕ} (hm : 3 ≤ m) (z : ℚ) :
    (b (m-1)/b m)*(z-1)^2*(h m).eval z =
      z^2*(h (m-2)).eval z+(1/2:ℚ)*((z-2)*(z+1)*(2*z-1))*(h (m-1)).eval z := by
  have hh := congrArg (Polynomial.eval z) (Recurrence.three_term_recurrence hm)
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat] using hh

/-- 将已证明的 P2 真正用于 g_m，而非将递推作为假设。 -/
theorem g_recurrence (n : ℕ) {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (b (n+2)/b (n+3))*g (n+3) z = g (n+1) z-tau z*g (n+2) z := by
  have he := recurrence_eval (m := n+3) (by omega) z
  rw [show n+3-1 = n+2 by omega, show n+3-2 = n+1 by omega] at he
  have hsq : (rho z)^2 = (z-1)^2/z^2 := by simp only [rho,div_pow]
  have ht : -tau z*rho z = ((1/2:ℚ)*((z-2)*(z+1)*(2*z-1)))/z^2 := by
    unfold tau rho
    field_simp [hz,sub_ne_zero.mpr hz1]
    <;> ring
  have hp2 : (rho z)^(n+2) = (rho z)^(n+1)*rho z := by rw [show n+2 = (n+1)+1 by omega,pow_succ]
  have hp3 : (rho z)^(n+3) = (rho z)^(n+1)*(rho z)^2 := by rw [← pow_add]
  unfold g
  rw [hp2,hp3,hsq]
  calc
    _ = (rho z)^(n+1)/z^2*((b (n+2)/b (n+3))*(z-1)^2*(h (n+3)).eval z) := by ring
    _ = _ := by
      rw [he]
      have hz2 : z^2 ≠ 0 := pow_ne_zero _ hz
      field_simp [hz2] at ht ⊢
      linear_combination -(rho z)^(n+1)*(h (n+2)).eval z*ht

/-- 现有 Casoratian 引理作用于两条实际 g 序列。 -/
theorem W_step (n : ℕ) {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (b (n+2)/b (n+3))*W (n+3) z = -W (n+2) z := by
  have h1 := g_recurrence n hz hz1
  have h2 := g_recurrence n (rho_ne_zero hz hz1) (rho_ne_one hz)
  rw [tau_rho hz hz1] at h2
  have hc := casoratian_step _ _ _ _ _ _ _ _ h1 h2
  simpa only [W,show n+3-1 = n+2 by omega,show n+2-1 = n+1 by omega] using hc

theorem W_initial {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    W 2 z = -(z^2-z+1)/(2*z*(z-1)) := by
  simp only [W,g,show 2-1 = 1 by omega,h_two,h_one,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_X,
    pow_one,rho_rho hz hz1]
  unfold rho
  field_simp [hz,sub_ne_zero.mpr hz1]
  <;> ring

/-- 归一化和初值已经闭合的任意阶 Casoratian。 -/
theorem W_explicit (n : ℕ) {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    W (n+2) z = (-1)^(n+1)*b (n+2)*(z^2-z+1)/(z*(z-1)) := by
  induction n with
  | zero =>
    rw [W_initial hz hz1]
    norm_num only [Nat.zero_add,pow_one,b_two]
    field_simp [hz,sub_ne_zero.mpr hz1]
    <;> ring
    <;> simp
  | succ n ih =>
    have hn1 : b (n+2) ≠ 0 := (b_pos _ (by omega)).ne'
    have hn2 : b (n+3) ≠ 0 := (b_pos _ (by omega)).ne'
    apply mul_left_cancel₀ (div_ne_zero hn1 hn2)
    simp only [Nat.succ_eq_add_one,show n+1+2 = n+3 by omega]
    rw [W_step n hz hz1,ih,show n+1+1 = (n+1)+1 by rfl,pow_succ]
    field_simp [hn1,hn2,hz,sub_ne_zero.mpr hz1]
    <;> ring

/-- 从 g 的行列式还原规范中的相邻阶成对表达式。 -/
theorem W_to_L (n : ℕ) {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    W (n+2) z = (-1)^(n+1)*L (n+2) z/(z^(n+1)*(z-1)) := by
  simp only [W,L,g,show n+2-1 = n+1 by omega,rho_rho hz hz1]
  unfold rho
  simp only [div_pow,pow_succ]
  field_simp [hz,sub_ne_zero.mpr hz1,pow_ne_zero n hz,pow_ne_zero n (sub_ne_zero.mpr hz1)]
  apply (div_eq_iff ?_).mpr
  · ring
  all_goals
    repeat' apply mul_ne_zero
    all_goals first | exact hz | exact sub_ne_zero.mpr hz1 | exact pow_ne_zero _ hz | exact pow_ne_zero _ (sub_ne_zero.mpr hz1)

/-- P3 正文 (2.9)，任意 m≥2，使用实际 h_m、b_m。 -/
theorem adjacent_pair {m : ℕ} (hm : 2 ≤ m) {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (h m).eval (rho z)*(h (m-1)).eval z+
      (z-1)^2/z*(h m).eval z*(h (m-1)).eval (rho z) =
        b m*z^(m-2)*(z^2-z+1) := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hm
  have he : m = n+2 := by omega
  rw [he,show n+2-2 = n by omega]
  change L (n+2) z = _
  have hs : (-1:ℚ)^(n+1)/(z^(n+1)*(z-1)) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero (pow_ne_zero _ hz) (sub_ne_zero.mpr hz1))
  apply mul_left_cancel₀ hs
  calc
    _ = W (n+2) z := by rw [W_to_L n hz hz1]; ring
    _ = _ := by
      rw [W_explicit n hz hz1,pow_succ]
      field_simp [hz,sub_ne_zero.mpr hz1]
      <;> ring

end CP.Adjacent

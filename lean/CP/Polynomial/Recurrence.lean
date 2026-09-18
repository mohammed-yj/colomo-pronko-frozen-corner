import CP.Polynomial.Fractional

namespace CP.Recurrence
open Polynomial Finset

/-- 实际 h_m 的归一化系数。 -/
noncomputable def coeff (m a : ℕ) : ℚ := (h m).coeff a / b m

/-- 负次数的有限替代；不会把自然数截断的 a-d 当成有效系数。 -/
noncomputable def shifted (m a d : ℕ) : ℚ := if d ≤ a then coeff m (a-d) else 0

theorem coeff_factorial {m a : ℕ} (hm : 1 ≤ m) (ha : a < m) :
    coeff m a = ((m+a-1).factorial : ℚ)*((2*m-a-2).factorial : ℚ) /
      ((a.factorial : ℚ)*((m-a-1).factorial : ℚ)*((2*m-2).factorial : ℚ)) :=
  normalized_coeff_factorial m a hm ha

theorem coeff_down_one {m a : ℕ} (ha : 1 ≤ a) (ham : a < m) :
    coeff m (a-1) =
      ((a:ℚ)*(2*m-a-1)/(((m:ℚ)+a-1)*(m-a)))*coeff m a := by
  have hc := Fractional.h_coeff_recurrence (m-1) (a-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.sub_add_cancel ha] at hc
  push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : 1 ≤ m)] at hc
  have hd1 : (m:ℚ)+a-1 ≠ 0 := by
    have ha' : (1:ℚ) ≤ a := by exact_mod_cast ha
    have hm' : (a:ℚ) < m := by exact_mod_cast ham
    linarith
  have hd2 : (m:ℚ)-a ≠ 0 := by exact sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast ham))
  unfold coeff
  have hb : b m ≠ 0 := (b_pos m (by omega)).ne'
  field_simp [hd1,hd2,hb]
  linear_combination b m * hc

/-- 相邻阶同次系数商；仅展开有限阶乘，并显式保护 a<m-1。 -/
theorem coeff_down_order (a r : ℕ) :
    coeff (a+r+1) a =
      (((r:ℚ)+1)*(2*((a:ℚ)+r+2)-2)*(2*((a:ℚ)+r+2)-3) /
        (((a:ℚ)+r+2+a-1)*(2*((a:ℚ)+r+2)-a-2)*(2*((a:ℚ)+r+2)-a-3))) *
        coeff (a+r+2) a := by
  rw [coeff_factorial (by omega) (by omega), coeff_factorial (by omega) (by omega)]
  have e1 : a+r+1+a-1 = 2*a+r := by omega
  have e2 : 2*(a+r+1)-a-2 = a+2*r := by omega
  have e3 : a+r+1-a-1 = r := by omega
  have e4 : 2*(a+r+1)-2 = 2*a+2*r := by omega
  have e5 : a+r+2+a-1 = 2*a+r+1 := by omega
  have e6 : 2*(a+r+2)-a-2 = a+2*r+2 := by omega
  have e7 : a+r+2-a-1 = r+1 := by omega
  have e8 : 2*(a+r+2)-2 = 2*a+2*r+2 := by omega
  rw [e1,e2,e3,e4,e5,e6,e7,e8]
  have hs : (((r:ℚ)+1)*(2*((a:ℚ)+r+2)-2)*(2*((a:ℚ)+r+2)-3) /
        (((a:ℚ)+r+2+a-1)*(2*((a:ℚ)+r+2)-a-2)*(2*((a:ℚ)+r+2)-a-3))) =
      ((r:ℚ)+1)*(2*a+2*r+2)*(2*a+2*r+1)/
        ((2*a+r+1)*(a+2*r+2)*(a+2*r+1)) := by congr 1 <;> ring
  rw [hs]
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp (disch := positivity)
  <;> ring

def u1 (m a : ℚ) : ℚ := a*(2*m-a-1)/((m+a-1)*(m-a))
def u2 (m a : ℚ) : ℚ := a*(a-1)*(2*m-a)*(2*m-a-1)/((m+a-2)*(m+a-1)*(m-a)*(m-a+1))
def v0 (m a : ℚ) : ℚ := (m-a-1)*(2*m-2)*(2*m-3)/((m+a-1)*(2*m-a-2)*(2*m-a-3))
def v1 (m a : ℚ) : ℚ := a*(2*m-2)*(2*m-3)/((m+a-1)*(m+a-2)*(2*m-a-2))
def v2 (m a : ℚ) : ℚ := a*(a-1)*(2*m-2)*(2*m-3)/((m+a-1)*(m+a-2)*(m+a-3)*(m-a))
def v3 (m a : ℚ) : ℚ := v2 m a*(a-2)*(2*m-a-1)/((m+a-4)*(m-a+1))
def w2 (m a : ℚ) : ℚ := a*(a-1)*(2*m-2)*(2*m-3)*(2*m-4)*(2*m-5)/
  ((m+a-4)*(m+a-3)*(m+a-2)*(m+a-1)*(2*m-a-3)*(2*m-a-2))

/-- 附录 A 的工作范围。 -/
def LowRange (m a : ℕ) : Prop := 5 ≤ m ∧ 2*a ≤ m+1

theorem lowRange_bounds {m a : ℕ} (h : LowRange m a) :
    (5:ℚ) ≤ m ∧ (0:ℚ) ≤ a ∧ (a:ℚ)+1 < m := by
  rcases h with ⟨hm,ha⟩
  constructor
  · exact_mod_cast hm
  constructor
  · positivity
  · exact_mod_cast (show a+1 < m by omega)

/-- 八个公共分母因子及 beta 的两个因子均非零。 -/
theorem denominator_factors {m a : ℕ} (h : LowRange m a) :
    (m:ℚ)-a ≠ 0 ∧ (m:ℚ)-a+1 ≠ 0 ∧ 2*(m:ℚ)-a-3 ≠ 0 ∧
    2*(m:ℚ)-a-2 ≠ 0 ∧ (a:ℚ)+m-1 ≠ 0 ∧ (a:ℚ)+m-2 ≠ 0 ∧
    (a:ℚ)+m-3 ≠ 0 ∧ (a:ℚ)+m-4 ≠ 0 ∧ 2*(m:ℚ)-5 ≠ 0 ∧ 2*(m:ℚ)-3 ≠ 0 := by
  rcases lowRange_bounds h with ⟨hm,ha,ham⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem ratio_u1 {m a : ℕ} (h : LowRange m a) :
    shifted m a 1 = u1 m a * coeff m a := by
  by_cases ha : a = 0
  · subst a; simp [shifted,u1]
  · rw [shifted, if_pos (by omega)]
    exact coeff_down_one (by omega) (by have := h.2; have := h.1; omega)

theorem coeff_down_order_general {m a : ℕ} (ha : a+2 ≤ m) :
    coeff (m-1) a = v0 m a * coeff m a := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le ha
  have hm : m = a+r+2 := by omega
  rw [hm]
  rw [show a+r+2-1 = a+r+1 by omega]
  convert coeff_down_order a r using 1 <;> unfold v0 <;> push_cast <;> ring

theorem ratio_v0 {m a : ℕ} (h : LowRange m a) :
    coeff (m-1) a = v0 m a * coeff m a :=
  coeff_down_order_general (by have := h.1; have := h.2; omega)

theorem ratio_u2 {m a : ℕ} (h : LowRange m a) :
    shifted m a 2 = u2 m a * coeff m a := by
  by_cases ha : 2 ≤ a
  · rw [shifted, if_pos ha]
    have h1 := coeff_down_one (m := m) (a := a) (by omega) (by have := h.2; have := h.1; omega)
    have h2 := coeff_down_one (m := m) (a := a-1) (by omega) (by have := h.2; have := h.1; omega)
    rw [show a-1-1 = a-2 by omega, h1] at h2
    rw [h2]
    unfold u2
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]
    rcases lowRange_bounds h with ⟨hm,ha0,ham⟩
    field_simp (disch := (repeat' apply mul_ne_zero; all_goals linarith))
    <;> ring
  · have he : a = 0 ∨ a = 1 := by omega
    rcases he with rfl | rfl <;> simp [shifted,u2]

theorem ratio_v1 {m a : ℕ} (h : LowRange m a) :
    shifted (m-1) a 1 = v1 m a * coeff m a := by
  by_cases ha : 1 ≤ a
  · rw [shifted, if_pos ha,
      coeff_down_one ha (by have := h.1; have := h.2; omega), ratio_v0 h]
    unfold v0 v1
    push_cast [Nat.cast_sub (by have := h.1; omega : 1 ≤ m)]
    rcases lowRange_bounds h with ⟨hm,ha0,ham⟩
    field_simp
    apply (div_eq_div_iff ?_ ?_).mpr
    · ring
    all_goals
      repeat' apply mul_ne_zero
      all_goals linarith
  · have he : a = 0 := by omega
    subst a
    simp [shifted,v1]

theorem ratio_v2 {m a : ℕ} (h : LowRange m a) :
    shifted (m-1) a 2 = v2 m a * coeff m a := by
  by_cases ha : 2 ≤ a
  · rw [shifted, if_pos ha]
    have h1 := ratio_v1 h
    rw [shifted, if_pos (by omega)] at h1
    have h2 := coeff_down_one (m := m-1) (a := a-1) (by omega)
      (by have := h.1; have := h.2; omega)
    rw [show a-1-1 = a-2 by omega, h1] at h2
    rw [h2]
    unfold v1 v2
    push_cast [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by have := h.1; omega : 1 ≤ m)]
    rcases lowRange_bounds h with ⟨hm,ha0,ham⟩
    field_simp
    apply (div_eq_div_iff ?_ ?_).mpr
    · ring
    all_goals
      repeat' apply mul_ne_zero
      all_goals linarith
  · have he : a = 0 ∨ a = 1 := by omega
    rcases he with rfl | rfl <;> simp [shifted,v2]

theorem ratio_v3 {m a : ℕ} (h : LowRange m a) :
    shifted (m-1) a 3 = v3 m a * coeff m a := by
  by_cases ha : 3 ≤ a
  · rw [shifted, if_pos ha]
    have h1 := ratio_v2 h
    rw [shifted, if_pos (by omega)] at h1
    have h2 := coeff_down_one (m := m-1) (a := a-2) (by omega)
      (by have := h.1; have := h.2; omega)
    rw [show a-2-1 = a-3 by omega, h1] at h2
    rw [h2]
    unfold v3 v2
    push_cast [Nat.cast_sub (by omega : 2 ≤ a), Nat.cast_sub (by have := h.1; omega : 1 ≤ m)]
    rcases lowRange_bounds h with ⟨hm,ha0,ham⟩
    field_simp
    apply (div_eq_div_iff ?_ ?_).mpr
    · ring
    all_goals
      repeat' apply mul_ne_zero
      all_goals linarith
  · have he : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    rcases he with rfl | rfl | rfl <;> simp [shifted,v3,v2]

theorem ratio_w2 {m a : ℕ} (h : LowRange m a) :
    shifted (m-2) a 2 = w2 m a * coeff m a := by
  by_cases ha : 2 ≤ a
  · rw [shifted, if_pos ha]
    have h1 := ratio_v2 h
    rw [shifted, if_pos ha] at h1
    have h2 := coeff_down_order_general (m := m-1) (a := a-2)
      (by have := h.1; have := h.2; omega)
    rw [show m-1-1 = m-2 by omega, h1] at h2
    rw [h2]
    unfold v0 v2 w2
    push_cast [Nat.cast_sub ha, Nat.cast_sub (by have := h.1; omega : 1 ≤ m)]
    rcases lowRange_bounds h with ⟨hm,ha0,ham⟩
    field_simp
    apply (div_eq_div_iff ?_ ?_).mpr
    · ring
    all_goals
      repeat' apply mul_ne_zero
      all_goals linarith
  · have he : a = 0 ∨ a = 1 := by omega
    rcases he with rfl | rfl <;> simp [shifted,w2]

/-- 规范 beta_(m-1) 的实际归一化。 -/
theorem beta_previous {m : ℕ} (hm : 5 ≤ m) :
    b (m-2)/b (m-1) = 3*(3*(m:ℚ)-7)*(3*(m:ℚ)-5)/
      (4*(2*(m:ℚ)-5)*(2*(m:ℚ)-3)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 5+n-2 = n+3 by omega, show 5+n-1 = n+4 by omega]
  have hb := beta_succ_three (n+1)
  simp only [Nat.add_assoc] at hb
  rw [hb]
  push_cast
  congr 1 <;> ring

/-- 八项有理恒等式；逐项乘公共分母后使用原有整数多项式证书。 -/
theorem ratio_certificate {m a : ℕ} (h : LowRange m a) :
    1-2*u1 m a+u2 m a-v0 m a+(3/2:ℚ)*v1 m a+(3/2:ℚ)*v2 m a-v3 m a-
      (b (m-2)/b (m-1))*w2 m a = 0 := by
  rw [beta_previous h.1]
  rcases lowRange_bounds h with ⟨hm,ha,ham⟩
  let M : ℚ := m
  let A : ℚ := a
  have d0 : (M-A) ≠ 0 := by dsimp [M,A]; linarith
  have d1 : (M-A+1) ≠ 0 := by dsimp [M,A]; linarith
  have d2 : (2*M-A-3) ≠ 0 := by dsimp [M,A]; linarith
  have d3 : (2*M-A-2) ≠ 0 := by dsimp [M,A]; linarith
  have d4 : (A+M-1) ≠ 0 := by dsimp [M,A]; linarith
  have d5 : (A+M-2) ≠ 0 := by dsimp [M,A]; linarith
  have d6 : (A+M-3) ≠ 0 := by dsimp [M,A]; linarith
  have d7 : (A+M-4) ≠ 0 := by dsimp [M,A]; linarith
  have d8 : (2*M-5) ≠ 0 := by dsimp [M,A]; linarith
  have d9 : (2*M-3) ≠ 0 := by dsimp [M,A]; linarith
  let D : ℚ := (M-A)*(M-A+1)*(2*M-A-3)*(2*M-A-2)*(A+M-1)*(A+M-2)*(A+M-3)*(A+M-4)
  let N1 : ℚ := -2*A*(A-2*M+1)*(A-2*M+2)*(A-2*M+3)*(A-M-1)*(A+M-4)*(A+M-3)*(A+M-2)
  let N2 : ℚ := A*(A-1)*(A-2*M)*(A-2*M+1)*(A-2*M+2)*(A-2*M+3)*(A+M-4)*(A+M-3)
  let N3 : ℚ := 2*(A-M)*(M-1)*(2*M-3)*(A-M-1)*(A-M+1)*(A+M-4)*(A+M-3)*(A+M-2)
  let N4 : ℚ := -3*A*(A-M)*(M-1)*(2*M-3)*(A-2*M+3)*(A-M-1)*(A+M-4)*(A+M-3)
  let N5 : ℚ := -3*A*(A-1)*(M-1)*(2*M-3)*(A-2*M+2)*(A-2*M+3)*(A-M-1)*(A+M-4)
  let N6 : ℚ := 2*A*(A-2)*(A-1)*(M-1)*(2*M-3)*(A-2*M+1)*(A-2*M+2)*(A-2*M+3)
  let N7 : ℚ := -3*A*(A-1)*(A-M)*(M-2)*(M-1)*(3*M-7)*(3*M-5)*(A-M-1)
  have hD : D ≠ 0 := by dsimp [D]; simp only [mul_ne_zero_iff]; tauto
  have e1 : (-2*u1 M A)*D = N1 := by
    dsimp [v3,u1,u2,v0,v1,v2,w2,D,N1]
    simp only [add_comm M A]
    field_simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9]
    <;> ring
  have e2 : (u2 M A)*D = N2 := by
    dsimp [v3,u1,u2,v0,v1,v2,w2,D,N2]
    simp only [add_comm M A]
    field_simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9]
    <;> ring
  have e3 : (-v0 M A)*D = N3 := by
    dsimp [v3,u1,u2,v0,v1,v2,w2,D,N3]
    simp only [add_comm M A]
    field_simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9]
    <;> ring
  have e4 : ((3/2:ℚ)*v1 M A)*D = N4 := by
    dsimp [v3,u1,u2,v0,v1,v2,w2,D,N4]
    simp only [add_comm M A]
    field_simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9]
    <;> ring
  have e5 : ((3/2:ℚ)*v2 M A)*D = N5 := by
    dsimp [v3,u1,u2,v0,v1,v2,w2,D,N5]
    simp only [add_comm M A]
    field_simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9]
    <;> ring
  have e6 : (-v3 M A)*D = N6 := by
    dsimp [v3,u1,u2,v0,v1,v2,w2,D,N6]
    simp only [add_comm M A]
    field_simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9]
    <;> ring
  have e7 : (-(3*(3*M-7)*(3*M-5)/(4*(2*M-5)*(2*M-3)))*w2 M A)*D = N7 := by
    dsimp [v3,u1,u2,v0,v1,v2,w2,D,N7]
    simp only [add_comm M A]
    field_simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9]
    <;> ring
  have hc : D+N1+N2+N3+N4+N5+N6+N7 = 0 := by
    dsimp [D,N1,N2,N3,N4,N5,N6,N7]
    linear_combination recurrence_certificate A M
  apply mul_right_cancel₀ hD
  rw [zero_mul]
  change (1-2*u1 M A+u2 M A-v0 M A+(3/2:ℚ)*v1 M A+(3/2:ℚ)*v2 M A-v3 M A-
    (3*(3*M-7)*(3*M-5)/(4*(2*M-5)*(2*M-3)))*w2 M A)*D = 0
  linear_combination e1+e2+e3+e4+e5+e6+e7+hc

/-- 七个系数商实际应用于 h_m 后，得到低次数上的三项递推。 -/
theorem low_coeff_recurrence {m a : ℕ} (h : LowRange m a) :
    coeff m a - 2*shifted m a 1 + shifted m a 2 =
      coeff (m-1) a - (3/2:ℚ)*shifted (m-1) a 1 - (3/2:ℚ)*shifted (m-1) a 2 +
        shifted (m-1) a 3 + (b (m-2)/b (m-1))*shifted (m-2) a 2 := by
  rw [ratio_u1 h, ratio_u2 h, ratio_v0 h, ratio_v1 h, ratio_v2 h, ratio_v3 h, ratio_w2 h]
  linear_combination coeff m a * ratio_certificate h

noncomputable def normalized (m : ℕ) : ℚ[X] := C ((b m)⁻¹)*h m
noncomputable def cubic : ℚ[X] := 1-C (3/2:ℚ)*X-C (3/2:ℚ)*X^2+X^3
noncomputable def recLeft (m : ℕ) : ℚ[X] := (1-X)^2*normalized m
noncomputable def recRight (m : ℕ) : ℚ[X] := cubic*normalized (m-1)+
  C (b (m-2)/b (m-1))*X^2*normalized (m-2)

theorem normalized_coeff (m a : ℕ) : (normalized m).coeff a = coeff m a := by
  rw [normalized, Polynomial.coeff_C_mul]
  unfold coeff
  rw [div_eq_mul_inv, mul_comm]

theorem shifted_coeff (m a d : ℕ) :
    (X^d*normalized m).coeff a = shifted m a d := by
  rw [Polynomial.coeff_X_pow_mul']
  simp only [shifted, normalized_coeff]

theorem recLeft_coeff (m a : ℕ) : (recLeft m).coeff a =
    coeff m a - 2*shifted m a 1+shifted m a 2 := by
  have he : recLeft m = normalized m-C (2:ℚ)*(X^1*normalized m)+X^2*normalized m := by
    unfold recLeft
    simp only [map_ofNat]
    ring
  rw [he]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    normalized_coeff, shifted_coeff]

theorem recRight_coeff (m a : ℕ) : (recRight m).coeff a =
    coeff (m-1) a - (3/2:ℚ)*shifted (m-1) a 1 - (3/2:ℚ)*shifted (m-1) a 2 +
      shifted (m-1) a 3 + (b (m-2)/b (m-1))*shifted (m-2) a 2 := by
  have he : recRight m = normalized (m-1)-C (3/2:ℚ)*(X^1*normalized (m-1))-
      C (3/2:ℚ)*(X^2*normalized (m-1))+X^3*normalized (m-1)+
      C (b (m-2)/b (m-1))*(X^2*normalized (m-2)) := by unfold recRight cubic; ring
  rw [he]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    normalized_coeff, shifted_coeff]

theorem normalized_degree {m : ℕ} (hm : 1 ≤ m) : (normalized m).natDegree ≤ m-1 := by
  have hh := h_natDegree_lt m hm
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by omega)

theorem normalized_reflect {m : ℕ} (hm : 1 ≤ m) :
    (normalized m).reflect (m-1) = normalized m := by
  unfold normalized
  rw [Polynomial.reflect_C_mul]
  have hh := Fractional.reflect_h (m-1)
  rw [Nat.sub_add_cancel hm] at hh
  rw [hh]

theorem cubic_reflect : cubic.reflect 3 = cubic := by
  have hx : (X:ℚ[X]) = X^1 := (pow_one X).symm
  unfold cubic
  conv_lhs => arg 2; rw [hx]
  simp only [Polynomial.reflect_add, Polynomial.reflect_sub, Polynomial.reflect_one,
    Polynomial.reflect_C_mul_X_pow, Polynomial.reflect_monomial,
    Polynomial.revAt_le (by omega : 1 ≤ 3), Polynomial.revAt_le (by omega : 2 ≤ 3),
    Polynomial.revAt_le (by omega : 3 ≤ 3)]
  norm_num
  ring

theorem recLeft_reflect {m : ℕ} (hm : 1 ≤ m) :
    (recLeft m).reflect (m+1) = recLeft m := by
  unfold recLeft
  rw [show m+1 = 2+(m-1) by omega,
    Polynomial.reflect_mul _ _ (Fractional.one_sub_X_pow_degree 2) (normalized_degree hm),
    Fractional.reflect_one_sub_X_pow, normalized_reflect hm]
  norm_num

theorem recRight_reflect {m : ℕ} (hm : 3 ≤ m) :
    (recRight m).reflect (m+1) = recRight m := by
  unfold recRight
  rw [Polynomial.reflect_add]
  have h1 := Polynomial.reflect_mul cubic (normalized (m-1))
    (by unfold cubic; compute_degree : cubic.natDegree ≤ 3) (normalized_degree (by omega : 1 ≤ m-1))
  rw [show 3+(m-1-1) = m+1 by omega, cubic_reflect, normalized_reflect (by omega)] at h1
  have h2 := Polynomial.reflect_mul (X^2:ℚ[X]) (normalized (m-2))
    (by simp : (X^2:ℚ[X]).natDegree ≤ 4) (normalized_degree (by omega : 1 ≤ m-2))
  rw [show 4+(m-2-1) = m+1 by omega, Polynomial.reflect_monomial,
    Polynomial.revAt_le (by omega : 2 ≤ 4), normalized_reflect (by omega)] at h2
  rw [h1, mul_assoc, Polynomial.reflect_C_mul, h2]

theorem recLeft_degree {m : ℕ} (hm : 1 ≤ m) : (recLeft m).natDegree ≤ m+1 := by
  have hh := normalized_degree hm
  have hw := Fractional.one_sub_X_pow_degree 2
  have hd : (recLeft m).natDegree ≤ ((1-X:ℚ[X])^2).natDegree+(normalized m).natDegree :=
    Polynomial.natDegree_mul_le
  omega

theorem recRight_degree {m : ℕ} (hm : 3 ≤ m) : (recRight m).natDegree ≤ m+1 := by
  have hh1 := normalized_degree (by omega : 1 ≤ m-1)
  have hh2 := normalized_degree (by omega : 1 ≤ m-2)
  have hc : cubic.natDegree ≤ 3 := by unfold cubic; compute_degree
  have hd1 : (cubic*normalized (m-1)).natDegree ≤ cubic.natDegree+(normalized (m-1)).natDegree :=
    Polynomial.natDegree_mul_le
  have hd2 : (X^2*normalized (m-2)).natDegree ≤ 2+(normalized (m-2)).natDegree := by
    exact le_trans Polynomial.natDegree_mul_le
      (Nat.add_le_add_right (Polynomial.natDegree_X_pow_le 2) _)
  have hd3 := Polynomial.natDegree_C_mul_le (a := b (m-2)/b (m-1)) (f := X^2*normalized (m-2))
  have hd4 := Polynomial.natDegree_add_le (cubic*normalized (m-1))
    (C (b (m-2)/b (m-1))*(X^2*normalized (m-2)))
  have he : recRight m = cubic*normalized (m-1)+C (b (m-2)/b (m-1))*(X^2*normalized (m-2)) := by
    unfold recRight; ring
  rw [he]
  omega

/-- 由低次数系数和合法范围的回文反射推出整个多项式递推。 -/
theorem normalized_recurrence_large {m : ℕ} (hm : 5 ≤ m) : recLeft m = recRight m := by
  ext a
  have hlo : ∀ a, 2*a ≤ m+1 → (recLeft m).coeff a = (recRight m).coeff a := by
    intro a ha
    rw [recLeft_coeff, recRight_coeff]
    exact low_coeff_recurrence ⟨hm,ha⟩
  by_cases ha : 2*a ≤ m+1
  · exact hlo a ha
  · by_cases ht : a ≤ m+1
    · have hl := congrArg (fun p : ℚ[X] => p.coeff (m+1-a)) (recLeft_reflect (by omega : 1 ≤ m))
      have hr := congrArg (fun p : ℚ[X] => p.coeff (m+1-a)) (recRight_reflect (by omega : 3 ≤ m))
      dsimp only at hl hr
      rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega),
        show m+1-(m+1-a) = a by omega] at hl hr
      rw [hl,hr]
      exact hlo _ (by omega)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (recLeft_degree (by omega)) (by omega)),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (recRight_degree (by omega)) (by omega))]

/-- 两个规定的低阶基例，直接检查整个多项式。 -/
theorem normalized_recurrence_three : recLeft 3 = recRight 3 := by
  have b3 : b 3 = (2/7:ℚ) := by norm_num [b,h,Finset.sum_range_succ,Nat.choose]
  have b4 : b 4 = (1/6:ℚ) := by norm_num [b,h,Finset.sum_range_succ,Nat.choose]
  ext a
  by_cases ha : a ≤ 4
  · rw [recLeft_coeff,recRight_coeff]
    interval_cases a <;> norm_num [shifted,coeff,h_coeff,b3,b4,Nat.choose,Polynomial.coeff_one,Polynomial.coeff_X]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (recLeft_degree (by omega)) (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (recRight_degree (by omega)) (by omega))]

theorem normalized_recurrence_four : recLeft 4 = recRight 4 := by
  have b3 : b 3 = (2/7:ℚ) := by norm_num [b,h,Finset.sum_range_succ,Nat.choose]
  have b4 : b 4 = (1/6:ℚ) := by norm_num [b,h,Finset.sum_range_succ,Nat.choose]
  ext a
  by_cases ha : a ≤ 5
  · rw [recLeft_coeff,recRight_coeff]
    interval_cases a <;> norm_num [shifted,coeff,h_coeff,b3,b4,Nat.choose,Polynomial.coeff_one,Polynomial.coeff_X]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (recLeft_degree (by omega)) (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (recRight_degree (by omega)) (by omega))]


theorem normalized_recurrence {m : ℕ} (hm : 3 ≤ m) : recLeft m = recRight m := by
  by_cases hlarge : 5 ≤ m
  · exact normalized_recurrence_large hlarge
  · have he : m = 3 ∨ m = 4 := by omega
    rcases he with rfl | rfl
    · exact normalized_recurrence_three
    · exact normalized_recurrence_four

/-- P2 正文 (2.6)：实际 h_m 序列的完整三项递推。 -/
theorem three_term_recurrence {m : ℕ} (hm : 3 ≤ m) :
    C (b (m-1)/b m)*(X-1)^2*h m =
      X^2*h (m-2)+C (1/2:ℚ)*((X-2)*(X+1)*(2*X-1))*h (m-1) := by
  have hn1 : b (m-1) ≠ 0 := (b_pos _ (by omega)).ne'
  have hn2 : b (m-2) ≠ 0 := (b_pos _ (by omega)).ne'
  have hb1 : C (b (m-1))*C ((b (m-1))⁻¹) = (1:ℚ[X]) := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hn1, Polynomial.C_1]
  have hb2 : C (b (m-2))*C ((b (m-2))⁻¹) = (1:ℚ[X]) := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hn2, Polynomial.C_1]
  have hl : C (b (m-1))*recLeft m = C (b (m-1)/b m)*(X-1)^2*h m := by
    unfold recLeft normalized
    rw [div_eq_mul_inv, Polynomial.C_mul]
    ring
  have hr : C (b (m-1))*recRight m = X^2*h (m-2)+cubic*h (m-1) := by
    unfold recRight normalized
    rw [div_eq_mul_inv, Polynomial.C_mul]
    calc
      _ = (C (b (m-1))*C ((b (m-1))⁻¹))*(cubic*h (m-1))+
          (C (b (m-2))*C ((b (m-2))⁻¹))*(C (b (m-1))*C ((b (m-1))⁻¹))*(X^2*h (m-2)) := by ring
      _ = _ := by rw [hb1,hb2]; ring
  have hc : cubic = C (1/2:ℚ)*((X-2)*(X+1)*(2*X-1)) := by
    have ht : C (3/2:ℚ) = (3:ℚ[X])*C (1/2:ℚ) := by
      rw [show (3/2:ℚ) = 3*(1/2) by ring, Polynomial.C_mul, map_ofNat]
    have ht2 : C (1/2:ℚ)*(2:ℚ[X]) = 1 := by
      rw [← map_ofNat Polynomial.C 2, ← Polynomial.C_mul]
      norm_num
    unfold cubic
    rw [ht]
    linear_combination -(X^3+1)*ht2
  rw [← hl, normalized_recurrence hm, hr, hc]

end CP.Recurrence

import Mathlib.Algebra.Polynomial.Reverse
import CP.Polynomial
import CP.BinomialMatrices
import Mathlib.Data.Nat.Choose.Vandermonde

/-! 精细多项式分式代换：有限求和、系数递推与系数缺口。 -/
namespace CP
namespace Fractional
open Polynomial Finset

/-- Chu–Vandermonde 在本项目需要的非负二项式参数化。 -/
def chuSum (r s k : ℕ) : ℕ :=
  ∑ a ∈ range (k+1), (r+a).choose a * (s-a).choose (k-a)

@[simp] theorem chuSum_zero (r s : ℕ) : chuSum r s 0 = 1 := by simp [chuSum]

theorem chuSum_step (r s k : ℕ) (hk : k ≤ s) :
    chuSum r (s+1) (k+1) = chuSum r s k + chuSum r s (k+1) := by
  unfold chuSum
  rw [sum_range_succ _ (k+1), sum_range_succ _ (k+1)]
  simp only [Nat.sub_self, Nat.choose_zero_right, mul_one]
  have hh : ∀ a ∈ range (k+1),
      (r+a).choose a * (s+1-a).choose (k+1-a) =
        (r+a).choose a * (s-a).choose (k-a) +
        (r+a).choose a * (s-a).choose (k+1-a) := by
    intro a ha
    have ha' : a ≤ k := by have := mem_range.mp ha; omega
    rw [show s+1-a = (s-a)+1 by omega,
      show k+1-a = (k-a)+1 by omega, Nat.choose_succ_succ', Nat.mul_add]
  simp_rw [sum_congr rfl hh, sum_add_distrib]
  omega

theorem chuSum_edge (r s : ℕ) : chuSum r s (s+1) = (r+s+1).choose (s+1) := by
  unfold chuSum
  rw [sum_range_succ _ (s+1)]
  have hz : ∑ a ∈ range (s+1), (r+a).choose a * (s-a).choose (s+1-a) = 0 := by
    apply sum_eq_zero
    intro a ha
    have ha' : a ≤ s := by have := mem_range.mp ha; omega
    rw [Nat.choose_eq_zero_of_lt (by omega : s-a < s+1-a), Nat.mul_zero]
  rw [hz]
  simp [Nat.add_assoc]

/-- 任意参数的有限 Chu–Vandermonde；包含端点 k=s。 -/
theorem finite_chu (r s k : ℕ) (hk : k ≤ s) :
    chuSum r s k = (r+s+1).choose k := by
  induction s generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp
  | succ s ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hks : k ≤ s := by omega
      rw [chuSum_step r s k hks, ih k hks]
      by_cases hlt : k < s
      · rw [ih (k+1) (by omega)]
        simpa [Nat.add_assoc] using (Nat.choose_succ_succ' (r+s+1) k).symm
      · have : k = s := by omega
        subst k
        rw [chuSum_edge]
        simpa [Nat.add_assoc] using (Nat.choose_succ_succ' (r+s+1) s).symm

/-- 原文 P，仍是有理系数多项式。 -/
noncomputable def gapPoly (q : ℕ) : ℚ[X] := (1-X)^(2*q+1)*h (q+1)

/-- 清除 (1-X)^q 后的真实分式代换；没有按待证系数定义。 -/
noncomputable def substPoly (q : ℕ) : ℚ[X] :=
  ∑ a ∈ range (q+1), C ((h (q+1)).coeff a * (-1)^a)*X^a*(1-X)^(q-a)

theorem h_succ_coeff {q a : ℕ} (ha : a ≤ q) :
    (h (q+1)).coeff a =
      ((q+a).choose a : ℚ)*((2*q-a).choose q : ℚ)/((3*q+1).choose q : ℚ) := by
  rw [h_coeff, if_pos (by omega)]
  have h1 : q+1+a-1 = q+a := by omega
  have h2 : 2*(q+1)-a-2 = 2*q-a := by omega
  have h3 : 3*(q+1)-2 = 3*q+1 := by omega
  rw [h1,h2,h3,Nat.add_sub_cancel, Nat.choose_symm_add]

theorem chu_product {q k a : ℕ} (ha : a ≤ k) (hk : k ≤ q) :
    (2*q-a).choose q * (q-a).choose (k-a) =
      (2*q-k).choose q * (2*q-a).choose (k-a) := by
  have hp := Nat.choose_mul (n := 2*q-a) (k := q-a) (s := k-a)
    (by omega) (by omega)
  have h1 : 2*q-a-(q-a) = q := by omega
  have h2 : 2*q-a-(k-a) = 2*q-k := by omega
  have h3 : q-a-(k-a) = q-k := by omega
  have h4 : 2*q-k-(q-k) = q := by omega
  rw [← Nat.choose_symm (by omega : q-a ≤ 2*q-a), h1, h2, h3,
    ← Nat.choose_symm (by omega : q-k ≤ 2*q-k), h4] at hp
  simpa [Nat.mul_comm] using hp

/-- 实际 h 系数上的有限 Chu 求和，是 (2.4) 的无升阶乘形式。 -/
theorem h_chu_sum {q k : ℕ} (hk : k ≤ q) :
    ∑ a ∈ range (k+1), (h (q+1)).coeff a * ((q-a).choose (k-a) : ℚ) =
      ((2*q-k).choose q : ℚ)*((3*q+1).choose k : ℚ)/((3*q+1).choose q : ℚ) := by
  have ht : ∀ a ∈ range (k+1),
      (h (q+1)).coeff a * ((q-a).choose (k-a) : ℚ) =
        (((2*q-k).choose q : ℚ)/((3*q+1).choose q : ℚ))*
          (((q+a).choose a : ℚ)*((2*q-a).choose (k-a) : ℚ)) := by
    intro a ha
    have hak : a ≤ k := by have := mem_range.mp ha; omega
    rw [h_succ_coeff (by omega : a ≤ q)]
    have hp : ((2*q-a).choose q : ℚ)*((q-a).choose (k-a) : ℚ) =
        ((2*q-k).choose q : ℚ)*((2*q-a).choose (k-a) : ℚ) := by
      exact_mod_cast chu_product hak hk
    calc
      _ = ((q+a).choose a : ℚ)*
          (((2*q-a).choose q : ℚ)*((q-a).choose (k-a) : ℚ))/((3*q+1).choose q : ℚ) := by ring
      _ = _ := by rw [hp]; ring
  rw [sum_congr rfl ht, ← mul_sum]
  have hs : ∑ a ∈ range (k+1), ((q+a).choose a : ℚ)*((2*q-a).choose (k-a) : ℚ) =
      ((3*q+1).choose k : ℚ) := by
    have hc := finite_chu q (2*q) k (by omega)
    unfold chuSum at hc
    rw [show q+2*q+1 = 3*q+1 by omega] at hc
    exact_mod_cast hc
  rw [hs]
  ring

/-- 显式 h 系数的一阶递推；边界以真正的零系数处理。 -/
theorem h_coeff_recurrence (q k : ℕ) :
    ((k:ℚ)+1)*((k:ℚ)-2*q)*(h (q+1)).coeff (k+1) =
      ((k:ℚ)-q)*((k:ℚ)+q+1)*(h (q+1)).coeff k := by
  by_cases hlt : k < q
  · rw [h_succ_coeff (by omega : k+1 ≤ q), h_succ_coeff (by omega : k ≤ q)]
    have h1 := Nat.succ_mul_choose_eq (q+k) k
    simp only [Nat.succ_eq_add_one] at h1
    have h2 := Nat.choose_mul_succ_eq (2*q-k-1) q
    have hn : 2*q-k-1+1 = 2*q-k := by omega
    have hnk : 2*q-k-q = q-k := by omega
    rw [hn,hnk] at h2
    have hp : (k+1)*(2*q-k)*(q+(k+1)).choose (k+1)*(2*q-(k+1)).choose q =
        (q-k)*(q+k+1)*(q+k).choose k*(2*q-k).choose q := by
      have hb : 2*q-(k+1) = 2*q-k-1 := by omega
      rw [hb]
      calc
        _ = ((q+k+1).choose (k+1)*(k+1))*
            ((2*q-k-1).choose q*(2*q-k)) := by rw [Nat.add_assoc]; ring
        _ = _ := by rw [← h1,h2]; ring
    have hp' := congrArg (fun n : ℕ => (n:ℚ)) hp
    push_cast [Nat.cast_sub (by omega : k ≤ 2*q), Nat.cast_sub (by omega : k ≤ q)] at hp'
    have hD : (((3*q+1).choose q : ℚ)) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : q ≤ 3*q+1)).ne'
    field_simp [hD]
    nlinarith [hp']
  · by_cases he : k = q
    · subst k
      simp [h_coeff]
    · have hk : q < k := by omega
      rw [h_coeff, h_coeff, if_neg (by omega), if_neg (by omega)]
      ring

/-- 单项的系数公式，显式保护负移位边界。 -/
theorem subst_term_coeff (q a k : ℕ) :
    (C ((h (q+1)).coeff a * (-1)^a)*X^a*(1-X)^(q-a)).coeff k =
      if a ≤ k then (-1)^k*(h (q+1)).coeff a*((q-a).choose (k-a) : ℚ) else 0 := by
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs with hak
  · rw [CP.coeff_one_sub_X_pow]
    have hs : (-1 : ℚ)^a * (-1)^(k-a) = (-1)^k := by
      rw [← pow_add, Nat.add_sub_of_le hak]
    calc
      _ = ((-1 : ℚ)^a * (-1)^(k-a))*(h (q+1)).coeff a*((q-a).choose (k-a) : ℚ) := by ring
      _ = _ := by rw [hs]
  · ring

theorem substPoly_degree (q : ℕ) : (substPoly q).natDegree ≤ q := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [substPoly, Polynomial.finset_sum_coeff]
  apply sum_eq_zero
  intro a ha
  have haq : a ≤ q := by have := mem_range.mp ha; omega
  rw [subst_term_coeff, if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega : q-a < k-a)]
  simp

/-- (2.4) 的实际系数等式；Chu 求和已经证明而非假设。 -/
theorem substPoly_coeff {q k : ℕ} (hk : k ≤ q) :
    (substPoly q).coeff k =
      (-1)^k*((2*q-k).choose q : ℚ)*((3*q+1).choose k : ℚ)/((3*q+1).choose q : ℚ) := by
  rw [substPoly, Polynomial.finset_sum_coeff]
  simp_rw [subst_term_coeff]
  have hr : (∑ a ∈ range (q+1),
      if a ≤ k then (-1)^k*(h (q+1)).coeff a*((q-a).choose (k-a) : ℚ) else 0) =
      ∑ a ∈ range (k+1),
        if a ≤ k then (-1)^k*(h (q+1)).coeff a*((q-a).choose (k-a) : ℚ) else 0 := by
    symm
    apply sum_subset (range_mono (by omega))
    intro a _ ha
    simp only [mem_range] at ha
    rw [if_neg (by omega)]
  rw [hr]
  have he : ∀ a ∈ range (k+1),
      (if a ≤ k then (-1)^k*(h (q+1)).coeff a*((q-a).choose (k-a) : ℚ) else 0) =
      (-1)^k*((h (q+1)).coeff a*((q-a).choose (k-a) : ℚ)) := by
    intro a ha
    rw [if_pos (by have := mem_range.mp ha; omega)]
    ring
  rw [sum_congr rfl he, ← mul_sum, h_chu_sum hk]
  ring

/-- 超几何微分算子的展开形式，方便逐项取有限多项式系数。 -/
noncomputable def hyperOp (a b c : ℚ) (p : ℚ[X]) : ℚ[X] :=
  X*p.derivative.derivative-X*(X*p.derivative.derivative)+
    C c*p.derivative-C (a+b+1)*(X*p.derivative)-C (a*b)*p

theorem hyperOp_coeff (a b c : ℚ) (p : ℚ[X]) (k : ℕ) :
    (hyperOp a b c p).coeff k =
      ((k:ℚ)+1)*((k:ℚ)+c)*p.coeff (k+1)-((k:ℚ)+a)*((k:ℚ)+b)*p.coeff k := by
  rcases k with _ | (_ | k)
  all_goals
    simp only [hyperOp, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero,
      Polynomial.coeff_derivative, Nat.succ_eq_add_one, Nat.cast_add,
      Nat.cast_zero, Nat.cast_one]
    ring

/-- 原文 h 的微分方程，直接由实际系数递推推出。 -/
theorem h_hyperOp (q : ℕ) :
    hyperOp (-(q:ℚ)) ((q:ℚ)+1) (-2*(q:ℚ)) (h (q+1)) = 0 := by
  ext k
  rw [hyperOp_coeff]
  simp only [Polynomial.coeff_zero]
  have hh := h_coeff_recurrence q k
  convert sub_eq_zero.mpr hh using 1 <;> ring

/-- 乘子 (1-X)^(2q+1) 对微分方程的具体变换。 -/
theorem gauge_succ (n : ℕ) (p : ℚ[X]) :
    hyperOp (-((n:ℚ)+1)) (-3*((n:ℚ)+1)-1) (-2*((n:ℚ)+1))
      ((1-X)^(2*n+3)*p) =
    (1-X)^(2*n+3)*hyperOp (-((n:ℚ)+1)) ((n:ℚ)+2) (-2*((n:ℚ)+1)) p := by
  simp only [hyperOp, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_add, Polynomial.derivative_neg,
    Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_X,
    Polynomial.derivative_C, zero_sub, sub_zero, zero_mul, add_zero]
  simp only [show 2*n+3-1 = 2*n+2 by omega, show 2*n+2-1 = 2*n+1 by omega,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Polynomial.C_add,
    Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_sub, Polynomial.C_1,
    map_ofNat, map_natCast, pow_succ]
  ring

/-- 变换后的实际多项式满足规范中的第二个微分方程。 -/
theorem gap_hyperOp {q : ℕ} (hq : 1 ≤ q) :
    hyperOp (-(q:ℚ)) (-3*(q:ℚ)-1) (-2*(q:ℚ)) (gapPoly q) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hg := gauge_succ n (h (n+1+1))
  have hh := h_hyperOp (n+1)
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at *
  rw [show (n:ℚ)+1+1 = (n:ℚ)+2 by ring] at hh
  rw [hh, mul_zero] at hg
  simpa only [gapPoly, show 2*(n+1)+1 = 2*n+3 by omega] using hg

theorem gap_coeff_recurrence {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    ((k:ℚ)+1)*((k:ℚ)-2*q)*(gapPoly q).coeff (k+1) =
      ((k:ℚ)-q)*((k:ℚ)-3*q-1)*(gapPoly q).coeff k := by
  have hc := congrArg (fun p : ℚ[X] => p.coeff k) (gap_hyperOp hq)
  dsimp only at hc
  rw [hyperOp_coeff, Polynomial.coeff_zero] at hc
  convert sub_eq_zero.mp hc using 1 <;> ring

theorem subst_coeff_recurrence {q k : ℕ} (hk : k < q) :
    ((k:ℚ)+1)*((k:ℚ)-2*q)*(substPoly q).coeff (k+1) =
      ((k:ℚ)-q)*((k:ℚ)-3*q-1)*(substPoly q).coeff k := by
  rw [substPoly_coeff (by omega : k+1 ≤ q), substPoly_coeff (by omega : k ≤ q)]
  have h1 := Nat.choose_succ_right_eq (3*q+1) k
  have h2 := Nat.choose_mul_succ_eq (2*q-k-1) q
  rw [show 2*q-k-1+1 = 2*q-k by omega,
    show 2*q-k-q = q-k by omega] at h2
  have hp : (k+1)*(2*q-k)*(2*q-(k+1)).choose q*(3*q+1).choose (k+1) =
      (q-k)*(3*q+1-k)*(2*q-k).choose q*(3*q+1).choose k := by
    rw [show 2*q-(k+1) = 2*q-k-1 by omega]
    calc
      _ = ((3*q+1).choose (k+1)*(k+1))*
          ((2*q-k-1).choose q*(2*q-k)) := by ring
      _ = _ := by rw [h1,h2]; ring
  have hp' := congrArg (fun n : ℕ => (n:ℚ)) hp
  push_cast [Nat.cast_sub (by omega : k ≤ 2*q),
    Nat.cast_sub (by omega : k ≤ q), Nat.cast_sub (by omega : k ≤ 3*q+1)] at hp'
  have hD : (((3*q+1).choose q : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : q ≤ 3*q+1)).ne'
  rw [pow_succ]
  convert congrArg (fun z : ℚ => (-1)^k*z/((3*q+1).choose q : ℚ)) hp' using 1 <;> ring

theorem gap_subst_coeff_zero (q : ℕ) :
    (gapPoly q).coeff 0 = (substPoly q).coeff 0 := by
  rw [substPoly_coeff (Nat.zero_le q)]
  simp [gapPoly, Polynomial.coeff_mul, coeff_one_sub_X_pow, h_succ_coeff (Nat.zero_le q)]

/-- 非奇异的低次数递推唯一确定 Q 的全部系数。 -/
theorem gap_subst_coeff {q : ℕ} (hq : 1 ≤ q) {k : ℕ} (hk : k ≤ q) :
    (gapPoly q).coeff k = (substPoly q).coeff k := by
  induction k with
  | zero => exact gap_subst_coeff_zero q
  | succ k ih =>
    have hne : ((k:ℚ)+1)*((k:ℚ)-2*q) ≠ 0 := by
      have hlt : (k:ℚ) < 2*q := by exact_mod_cast (show k < 2*q by omega)
      have hpos : (0:ℚ) < (k:ℚ)+1 := by positivity
      exact mul_ne_zero (ne_of_gt hpos) (sub_ne_zero.mpr (ne_of_lt hlt))
    apply mul_left_cancel₀ hne
    rw [gap_coeff_recurrence hq, subst_coeff_recurrence (by omega), ih (by omega)]

/-- 系数缺口；递推只在 k < 2q 处使用，不跨越其奇点。 -/
theorem gap_coeff_vanish {q : ℕ} (hq : 1 ≤ q) {k : ℕ}
    (hlo : q < k) (hhi : k ≤ 2*q) : (gapPoly q).coeff k = 0 := by
  have hz : (gapPoly q).coeff (q+1) = 0 := by
    have hc := gap_coeff_recurrence hq q
    have hne : ((q:ℚ)+1)*((q:ℚ)-2*q) ≠ 0 := by
      have hp : (0:ℚ) < q := by exact_mod_cast hq
      apply mul_ne_zero <;> linarith
    have hc' : ((q:ℚ)+1)*((q:ℚ)-2*q)*(gapPoly q).coeff (q+1) = 0 := by
      simpa using hc
    exact (mul_eq_zero.mp hc').resolve_left hne
  have hl : q+1 ≤ k := by omega
  induction k, hl using Nat.le_induction with
  | base => exact hz
  | succ k hk ih =>
    have hc := gap_coeff_recurrence hq k
    rw [ih (by omega) (by omega)] at hc
    have hne : ((k:ℚ)+1)*((k:ℚ)-2*q) ≠ 0 := by
      have ht : (k:ℚ) < 2*q := by exact_mod_cast (show k < 2*q by omega)
      have hp : (0:ℚ) < (k:ℚ)+1 := by positivity
      apply mul_ne_zero <;> linarith
    exact (mul_eq_zero.mp (by simpa using hc)).resolve_left hne

/-- 原文回文性，使用显式有限反序而非未声明的精确次数。 -/
theorem reflect_h (q : ℕ) : (h (q+1)).reflect q = h (q+1) := by
  ext k
  rw [Polynomial.coeff_reflect]
  by_cases hk : k ≤ q
  · rw [Polynomial.revAt_le hk]
    simpa using h_coeff_palindrome (q+1) k (by omega) (by omega)
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)]

theorem one_sub_X_pow_degree (n : ℕ) :
    ((1-X : ℚ[X])^n).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_one_sub_X_pow, Nat.choose_eq_zero_of_lt hk]
  simp

theorem reflect_one_sub_X_pow (n : ℕ) :
    ((1-X : ℚ[X])^n).reflect n = C ((-1:ℚ)^n)*(1-X)^n := by
  induction n with
  | zero => simp [Polynomial.reflect_one]
  | succ n ih =>
    rw [pow_succ, Polynomial.reflect_mul _ _ (one_sub_X_pow_degree n)
      (by simpa using one_sub_X_pow_degree 1), ih]
    simp only [Polynomial.reflect_sub, Polynomial.reflect_one,
      Polynomial.reflect_one_X, pow_one, pow_succ, Polynomial.C_mul,
      Polynomial.C_neg, Polynomial.C_1]
    ring

theorem gap_degree (q : ℕ) : (gapPoly q).natDegree ≤ 3*q+1 := by
  have hh : (h (q+1)).natDegree ≤ q := by have := h_natDegree_lt (q+1) (by omega); omega
  have hd : (((1-X:ℚ[X])^(2*q+1)) * h (q+1)).natDegree ≤
      ((1-X:ℚ[X])^(2*q+1)).natDegree + (h (q+1)).natDegree := Polynomial.natDegree_mul_le
  have hw := one_sub_X_pow_degree (2*q+1)
  unfold gapPoly
  omega

theorem gap_reflect (q : ℕ) : (gapPoly q).reflect (3*q+1) = -gapPoly q := by
  have hh : (h (q+1)).natDegree ≤ q := by have := h_natDegree_lt (q+1) (by omega); omega
  unfold gapPoly
  rw [show 3*q+1 = (2*q+1)+q by omega,
    Polynomial.reflect_mul _ _ (one_sub_X_pow_degree (2*q+1)) hh,
    reflect_one_sub_X_pow, reflect_h]
  have hs : (-1:ℚ)^(2*q+1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hs]
  simp

/-- P1 的完整有限多项式分解；包括此前缺少的高次项。 -/
theorem gap_decomposition {q : ℕ} (hq : 1 ≤ q) :
    gapPoly q = substPoly q - (substPoly q).reflect (3*q+1) := by
  ext k
  rw [Polynomial.coeff_sub, Polynomial.coeff_reflect]
  have qzero : ∀ j, q < j → (substPoly q).coeff j = 0 := by
    intro j hj
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (substPoly_degree q) hj)
  by_cases hk : k ≤ q
  · rw [Polynomial.revAt_le (by omega), qzero (3*q+1-k) (by omega), sub_zero]
    exact gap_subst_coeff hq hk
  · by_cases hm : k ≤ 2*q
    · rw [Polynomial.revAt_le (by omega), qzero _ (by omega), qzero _ (by omega),
        gap_coeff_vanish hq (by omega) hm, sub_self]
    · by_cases ht : k ≤ 3*q+1
      · rw [Polynomial.revAt_le ht, qzero _ (by omega), zero_sub]
        have hr := congrArg (fun p : ℚ[X] => p.coeff (3*q+1-k)) (gap_reflect q)
        dsimp only at hr
        rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega),
          show 3*q+1-(3*q+1-k) = k by omega, Polynomial.coeff_neg,
          gap_subst_coeff hq (k := 3*q+1-k) (by omega)] at hr
        exact hr
      · rw [Polynomial.revAt_eq_self_of_lt (by omega), sub_self]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (gap_degree q) (by omega))

/-- 原点截断的有限系数版本：模 X^(2q+1) 的余式完全相同。 -/
theorem gap_truncation {q : ℕ} (hq : 1 ≤ q) :
    X^(2*q+1) ∣ gapPoly q - substPoly q := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  rw [Polynomial.coeff_sub]
  by_cases hl : k ≤ q
  · rw [gap_subst_coeff hq hl, sub_self]
  · rw [gap_coeff_vanish hq (by omega) (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (substPoly_degree q) (by omega)), sub_self]

theorem h_comp_expansion (q : ℕ) (p : ℚ[X]) :
    (h (q+1)).comp p = ∑ a ∈ range (q+1), C ((h (q+1)).coeff a)*p^a := by
  conv_lhs => rw [Polynomial.as_sum_range' _ (q+1) (h_natDegree_lt _ (by omega))]
  simp only [Polynomial.sum_comp, Polynomial.monomial_comp]

theorem subst_term_reflect {q a : ℕ} (ha : a ≤ q) :
    (C ((h (q+1)).coeff a * (-1)^a)*X^a*(1-X)^(q-a)).reflect q =
      C ((-1:ℚ)^q)*C ((h (q+1)).coeff a)*(1-X)^(q-a) := by
  rw [mul_assoc, Polynomial.reflect_C_mul]
  have hm := Polynomial.reflect_mul (X^a : ℚ[X]) ((1-X)^(q-a))
    (by simp : (X^a : ℚ[X]).natDegree ≤ a) (one_sub_X_pow_degree (q-a))
  rw [Nat.add_sub_of_le ha] at hm
  rw [hm, Polynomial.reflect_monomial, Polynomial.revAt_le (le_refl a), Nat.sub_self,
    pow_zero, one_mul, reflect_one_sub_X_pow, ← mul_assoc, ← Polynomial.C_mul]
  have hs : (h (q+1)).coeff a * (-1)^a * (-1)^(q-a) =
      (-1:ℚ)^q*(h (q+1)).coeff a := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le ha]
    ring
  rw [hs, Polynomial.C_mul]

theorem subst_reflect (q : ℕ) :
    (substPoly q).reflect q = C ((-1:ℚ)^q)*(h (q+1)).comp (1-X) := by
  have hs : (substPoly q).reflect q = ∑ a ∈ range (q+1),
      (C ((h (q+1)).coeff a * (-1)^a)*X^a*(1-X)^(q-a)).reflect q := by
    ext k
    simp only [substPoly, Polynomial.coeff_reflect, Polynomial.finset_sum_coeff]
  rw [hs]
  have ht := sum_congr rfl (fun a (ha : a ∈ range (q+1)) =>
    subst_term_reflect (show a ≤ q by have := mem_range.mp ha; omega))
  rw [ht]
  simp_rw [mul_assoc]
  rw [← mul_sum]
  congr 1
  have hr := sum_range_reflect (fun a => C ((h (q+1)).coeff a)*(1-X : ℚ[X])^a) (q+1)
  simp only [Nat.add_sub_cancel] at hr
  rw [h_comp_expansion, ← hr]
  apply sum_congr rfl
  intro a ha
  rw [show (h (q+1)).coeff (q-a) = (h (q+1)).coeff a by
    simpa using h_coeff_palindrome (q+1) a (by omega) (mem_range.mp ha)]

/-- 分式代换的清分母恒等式，对每个 q（包括 q=0）成立。 -/
theorem fractional_cleared (q : ℕ) :
    substPoly q = (1-X)^(2*q+1)*h (q+1) +
      C ((-1:ℚ)^q)*X^(2*q+1)*(h (q+1)).comp (1-X) := by
  by_cases hq : q = 0
  · subst q
    simp [substPoly, h_one]
  · have hd := gap_decomposition (by omega : 1 ≤ q)
    have hr := Polynomial.reflect_mul (1:ℚ[X]) (substPoly q)
      (by simp : (1:ℚ[X]).natDegree ≤ 2*q+1) (substPoly_degree q)
    simp only [one_mul, Polynomial.reflect_one, show 2*q+1+q = 3*q+1 by omega,
      subst_reflect] at hr
    rw [hr] at hd
    unfold gapPoly at hd
    linear_combination -hd

theorem h_eval_expansion (q : ℕ) (t : ℚ) :
    (h (q+1)).eval t = ∑ a ∈ range (q+1), (h (q+1)).coeff a*t^a := by
  have hh := congrArg (Polynomial.eval t) (h_comp_expansion q X)
  simpa only [Polynomial.comp_X, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using hh

/-- substPoly 确实由实际分式代换清分母得到，并非按目标系数定义。 -/
theorem substPoly_eval (q : ℕ) (t : ℚ) (ht : t ≠ 1) :
    (substPoly q).eval t = (1-t)^q*(h (q+1)).eval (t/(t-1)) := by
  have hn : 1-t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hr : t/(t-1) = -t/(1-t) := by field_simp [sub_ne_zero.mpr ht, hn]; ring
  rw [h_eval_expansion, mul_sum]
  simp only [substPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  apply sum_congr rfl
  intro a ha
  have haq : a ≤ q := by have := mem_range.mp ha; omega
  have hs : (1-t)^q = (1-t)^a*(1-t)^(q-a) := by rw [← pow_add, Nat.add_sub_of_le haq]
  rw [hr, div_pow, neg_pow, hs]
  field_simp
  <;> ring

/-- 规范中的 Phi；输入 t=1 不属于分式恒等式的定义域。 -/
noncomputable def phi (m : ℕ) (t : ℚ) : ℚ := (h m).eval (t/(t-1))

/-- P1 正文 (2.1)，任意 m≥1 的实际 h_m 分式代换。 -/
theorem fractional_substitution (m : ℕ) (hm : 1 ≤ m) (t : ℚ) (ht : t ≠ 1) :
    phi m t = (1-t)^m*(h m).eval t +
      (-1)^(m-1)*t^(2*m-1)/(1-t)^(m-1)*(h m).eval (1-t) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, show 2*(q+1)-1 = 2*q+1 by omega]
  have hc := congrArg (Polynomial.eval t) (fractional_cleared q)
  rw [substPoly_eval q t ht] at hc
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_comp] at hc
  have hn : (1-t)^q ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm ht))
  apply mul_left_cancel₀ hn
  unfold phi
  rw [hc]
  rw [mul_add]
  have hs : (1-t)^(2*q+1) = (1-t)^q*(1-t)^(q+1) := by rw [← pow_add]; congr 1 <;> omega
  rw [hs]
  field_simp
  <;> ring

/-- 清分母后的原点余式；(1-X)^q 的常数项为 1，故这是 (2.2) 的有限实现。 -/
theorem fractional_truncation (m : ℕ) (hm : 1 ≤ m) :
    X^(2*m-1) ∣ substPoly (m-1) - (1-X)^(2*m-1)*h m := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, show 2*(q+1)-1 = 2*q+1 by omega]
  rw [fractional_cleared, add_sub_cancel_left]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem substitution_denominator_constant (q : ℕ) :
    ((1-X : ℚ[X])^q).coeff 0 = 1 := by simp [coeff_one_sub_X_pow]

end Fractional
end CP

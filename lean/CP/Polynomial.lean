import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# Polynomial definitions and algebraic certificates

The definitions use the manuscript's normalization. The results below prove
local algebraic certificates and substitutions. They do not assert P1, P2 or P3
for the entire explicitly defined sequence `h`.
-/
namespace CP
open Polynomial Finset

/-- The refined enumeration polynomial, with an explicit zero value at m = 0. -/
noncomputable def h (m : ℕ) : ℚ[X] :=
  ∑ a ∈ range m, C (((m + a - 1).choose (m - 1) : ℚ) *
    ((2 * m - a - 2).choose (m - 1) : ℚ) /
    ((3 * m - 2).choose (m - 1) : ℚ)) * X ^ a

noncomputable def b (m : ℕ) : ℚ := (h m).coeff 0

@[simp] theorem h_zero : h 0 = 0 := by simp [h]
@[simp] theorem h_one : h 1 = 1 := by norm_num [h, Finset.sum_range_succ]
@[simp] theorem h_two : h 2 = C (1 / 2 : ℚ) * (1 + X) := by
  norm_num [h, Finset.sum_range_succ]
  ring
@[simp] theorem b_one : b 1 = 1 := by simp [b]
@[simp] theorem b_two : b 2 = 1 / 2 := by simp [b]

/-- Nonzero denominators in the explicit coefficient formula (all positive m). -/
theorem h_denominator_pos {m : ℕ} (hm : 1 ≤ m) :
    (0 : ℚ) < ((3 * m - 2).choose (m - 1) : ℚ) := by
  exact_mod_cast Nat.choose_pos (by omega : m - 1 ≤ 3 * m - 2)

/-- Exact coefficients, with the support condition built into the statement. -/
theorem h_coeff (m a : ℕ) : (h m).coeff a =
    if a < m then ((m+a-1).choose (m-1) : ℚ) *
      ((2*m-a-2).choose (m-1) : ℚ) / ((3*m-2).choose (m-1) : ℚ)
    else 0 := by
  simp [h, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, Finset.sum_ite_eq']

theorem b_formula (m : ℕ) (hm : 1 ≤ m) :
    b m = ((2*m-2).choose (m-1) : ℚ) / ((3*m-2).choose (m-1) : ℚ) := by
  simp [b, h_coeff, show 0 < m by omega]

theorem b_pos (m : ℕ) (hm : 1 ≤ m) : 0 < b m := by
  rw [b_formula m hm]
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : m-1 ≤ 2*m-2)
  · exact h_denominator_pos hm

theorem h_natDegree_lt (m : ℕ) (hm : 1 ≤ m) : (h m).natDegree < m := by
  have hh : (h m).natDegree ≤ m-1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro a ha
    rw [h_coeff, if_neg (by omega)]
  omega

/-- The coefficient palindrome is proved from the explicit binomial formula. -/
theorem h_coeff_palindrome (m a : ℕ) (hm : 1 ≤ m) (ha : a < m) :
    (h m).coeff (m-1-a) = (h m).coeff a := by
  rw [h_coeff, h_coeff, if_pos ha, if_pos (by omega)]
  have h1 : m+(m-1-a)-1 = 2*m-a-2 := by omega
  have h2 : 2*m-(m-1-a)-2 = m+a-1 := by omega
  rw [h1,h2,mul_comm]

/-- Factorial normalization, derived from the two binomial factors. -/
theorem b_factorial (m : ℕ) (hm : 1 ≤ m) :
    b m = ((2*m-2).factorial : ℚ) * ((2*m-1).factorial : ℚ) /
      (((m-1).factorial : ℚ) * ((3*m-2).factorial : ℚ)) := by
  rw [b_formula m hm, Nat.cast_choose ℚ (by omega : m-1 ≤ 2*m-2),
    Nat.cast_choose ℚ (by omega : m-1 ≤ 3*m-2)]
  have h1 : 2*m-2-(m-1) = m-1 := by omega
  have h2 : 3*m-2-(m-1) = 2*m-1 := by omega
  rw [h1,h2]
  field_simp
  ring

/-- The factorial coefficients to which Appendix A must be connected. -/
theorem normalized_coeff_factorial (m a : ℕ) (hm : 1 ≤ m) (ha : a < m) :
    (h m).coeff a / b m =
      ((m+a-1).factorial : ℚ) * ((2*m-a-2).factorial : ℚ) /
      (((a).factorial : ℚ) * ((m-a-1).factorial : ℚ) * ((2*m-2).factorial : ℚ)) := by
  rw [h_coeff, if_pos ha, b_factorial m hm]
  rw [Nat.cast_choose ℚ (by omega : m-1 ≤ m+a-1),
    Nat.cast_choose ℚ (by omega : m-1 ≤ 2*m-a-2),
    Nat.cast_choose ℚ (by omega : m-1 ≤ 3*m-2)]
  have h1 : m+a-1-(m-1) = a := by omega
  have h2 : 2*m-a-2-(m-1) = m-a-1 := by omega
  have h3 : 3*m-2-(m-1) = 2*m-1 := by omega
  rw [h1,h2,h3]
  field_simp
  ring

/-- The recurrence normalization for all m ≥ 3, parameterized as m=n+3. -/
theorem beta_succ_three (n : ℕ) :
    b (n+2) / b (n+3) =
      3*(3*(n:ℚ)+5)*(3*(n:ℚ)+7) / (4*(2*(n:ℚ)+3)*(2*(n:ℚ)+5)) := by
  rw [b_factorial (n+2) (by omega), b_factorial (n+3) (by omega)]
  norm_num [Nat.mul_add, Nat.add_sub_assoc, Nat.factorial_succ, Nat.cast_add, Nat.cast_mul]
  field_simp
  <;> ring

/-- The order-three Möbius transformation in P3. -/
def rho (z : ℚ) : ℚ := (z - 1) / z

def tau (z : ℚ) : ℚ := -((z - 2) * (z + 1) * (2 * z - 1)) / (2 * z * (z - 1))

theorem rho_ne_zero {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) : rho z ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr hz1) hz

theorem rho_ne_one {z : ℚ} (hz : z ≠ 0) : rho z ≠ 1 := by
  unfold rho
  intro he
  have := (div_eq_iff hz).mp he
  linarith

theorem rho_rho {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    rho (rho z) = -1 / (z - 1) := by
  unfold rho
  field_simp [hz, sub_ne_zero.mpr hz1]

theorem rho_order_three {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    rho (rho (rho z)) = z := by
  rw [rho_rho hz hz1]
  unfold rho
  field_simp [hz, sub_ne_zero.mpr hz1]
  ring

theorem tau_rho {z : ℚ} (hz : z ≠ 0) (hz1 : z ≠ 1) : tau (rho z) = tau z := by
  unfold tau rho
  field_simp [hz, sub_ne_zero.mpr hz1]
  ring

/-- Casoratian propagation for two solutions of the same recurrence.
This lemma is algebraic; applying it to h still requires P2. -/
theorem casoratian_step (β τ a₀ a₁ a₂ b₀ b₁ b₂ : ℚ)
    (ha : β * a₂ = a₀ - τ * a₁) (hb : β * b₂ = b₀ - τ * b₁) :
    β * (a₂ * b₁ - a₁ * b₂) = -(a₁ * b₀ - a₀ * b₁) := by
  calc
    _ = (β * a₂) * b₁ - a₁ * (β * b₂) := by ring
    _ = _ := by rw [ha, hb]; ring

/-- The quadratic Plücker identity used in the polynomial-kernel calculation. -/
theorem plucker (a b c d e f g k : ℚ) :
    (a * d - b * c) * (e * k - f * g) -
      (a * f - b * e) * (c * k - d * g) +
      (a * k - b * g) * (c * f - d * e) = 0 := by ring

/-- Appendix A: one polynomial identity in arbitrary a and m, not a sample test. -/
theorem recurrence_certificate (a m : ℚ) :
    (m-a)*(m-a+1)*(2*m-a-3)*(2*m-a-2)*
      (a+m-1)*(a+m-2)*(a+m-3)*(a+m-4)
    - 2*a*(a-2*m+1)*(a-2*m+2)*(a-2*m+3)*(a-m-1)*
      (a+m-4)*(a+m-3)*(a+m-2)
    + a*(a-1)*(a-2*m)*(a-2*m+1)*(a-2*m+2)*(a-2*m+3)*
      (a+m-4)*(a+m-3)
    + 2*(a-m)*(m-1)*(2*m-3)*(a-m-1)*(a-m+1)*
      (a+m-4)*(a+m-3)*(a+m-2)
    - 3*a*(a-m)*(m-1)*(2*m-3)*(a-2*m+3)*(a-m-1)*
      (a+m-4)*(a+m-3)
    - 3*a*(a-1)*(m-1)*(2*m-3)*(a-2*m+2)*(a-2*m+3)*
      (a-m-1)*(a+m-4)
    + 2*a*(a-2)*(a-1)*(m-1)*(2*m-3)*(a-2*m+1)*
      (a-2*m+2)*(a-2*m+3)
    - 3*a*(a-1)*(a-m)*(m-2)*(m-1)*(3*m-7)*(3*m-5)*(a-m-1) = 0 := by
  ring

end CP

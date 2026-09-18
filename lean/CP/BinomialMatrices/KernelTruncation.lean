import CP.BinomialMatrices.Truncation

namespace CP.Series
open Polynomial Finset Matrix

noncomputable def rationalKernel (q : ℕ) : PowerSeries ℚ[X] :=
  negPower ℚ[X] q * PowerSeries.rescale (1+Polynomial.X) (negPower ℚ[X] 1)

/-- 该级数确实是规范 (6.6) 中分母的逆。 -/
theorem rationalKernel_denominator (q : ℕ) :
    (1+PowerSeries.X : PowerSeries ℚ[X])^q *
      (1+PowerSeries.X+PowerSeries.X*PowerSeries.C ℚ[X] Polynomial.X) * rationalKernel q = 1 := by
  have h0 : (1+PowerSeries.X : PowerSeries ℚ[X])^q*negPower ℚ[X] q = 1 := by
    simpa using negPower_cancel ℚ[X] 0 q
  have h1 := congrArg (PowerSeries.rescale (1+Polynomial.X : ℚ[X]))
    (negPower_one_inverse ℚ[X])
  simp only [map_mul, map_add, map_one, PowerSeries.rescale_X] at h1
  have h2 : (1+PowerSeries.X+PowerSeries.X*PowerSeries.C ℚ[X] Polynomial.X)*
      PowerSeries.rescale (1+Polynomial.X) (negPower ℚ[X] 1) = 1 := by
    convert h1 using 1 <;> ring
  unfold rationalKernel
  calc
    _ = ((1+PowerSeries.X)^q*negPower ℚ[X] q)*
        ((1+PowerSeries.X+PowerSeries.X*PowerSeries.C ℚ[X] Polynomial.X)*
          PowerSeries.rescale (1+Polynomial.X) (negPower ℚ[X] 1)) := by ring
    _ = _ := by rw [h0, h2, one_mul]

theorem negPower_coeff_C (d i : ℕ) :
    PowerSeries.coeff ℚ[X] i (negPower ℚ[X] d) =
      Polynomial.C (PowerSeries.coeff ℚ i (negPower ℚ d)) := by
  cases d with
  | zero => simp
  | succ d =>
    simp only [Nat.succ_eq_add_one, negPower_coeff]
    simp

noncomputable def geometricColumn (j : ℕ) : PowerSeries ℚ :=
  PowerSeries.C ℚ ((-1)^j)*PowerSeries.X^j*negPower ℚ (j+1)

theorem geometricColumn_coeff (j i : ℕ) :
    PowerSeries.coeff ℚ i (geometricColumn j) = (-1)^i*(i.choose j : ℚ) := by
  rw [geometricColumn, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hj : j ≤ i
  · rw [if_pos hj, negPower_coeff,
      show i-j+j = i by omega, Nat.choose_symm hj, ← mul_assoc, ← pow_add,
      show j+(i-j) = i by omega]
  · rw [if_neg hj, Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem rescaled_geometric_coeff (i j : ℕ) :
    (PowerSeries.coeff ℚ[X] i
      (PowerSeries.rescale (1+Polynomial.X) (negPower ℚ[X] 1))).coeff j =
        PowerSeries.coeff ℚ i (geometricColumn j) := by
  rw [PowerSeries.coeff_rescale, show 1 = 0+1 by rfl, negPower_coeff]
  simp only [Nat.add_zero, Nat.choose_self, Nat.cast_one, mul_one]
  have hs : (-1:ℚ[X])^i = Polynomial.C ((-1:ℚ)^i) := by simp
  rw [hs, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow, geometricColumn_coeff]
  ring

theorem rationalKernel_coeff (q i j : ℕ) :
    (PowerSeries.coeff ℚ[X] i (rationalKernel q)).coeff j =
      if j ≤ i then (-1)^i*((q+i).choose (i-j):ℚ) else 0 := by
  have hc : (PowerSeries.coeff ℚ[X] i (rationalKernel q)).coeff j =
      PowerSeries.coeff ℚ i (negPower ℚ q*geometricColumn j) := by
    rw [rationalKernel, PowerSeries.coeff_mul, Polynomial.finset_sum_coeff,
      PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [negPower_coeff_C, Polynomial.coeff_C_mul, rescaled_geometric_coeff]
  have hp : negPower ℚ q*geometricColumn j =
      PowerSeries.C ℚ ((-1)^j)*PowerSeries.X^j*negPower ℚ (q+j+1) := by
    rw [show q+j+1 = q+(j+1) by omega, negPower_add, geometricColumn]
    ring
  rw [hc, hp, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hj : j ≤ i
  · rw [if_pos hj, negPower_coeff,
      show i-j+(q+j) = q+i by omega, ← mul_assoc, ← pow_add,
      show j+(i-j) = i by omega]
    simp [hj]
  · simp [hj]

theorem rationalKernel_coeff_degree (q i : ℕ) :
    (PowerSeries.coeff ℚ[X] i (rationalKernel q)).natDegree ≤ i := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [rationalKernel_coeff, if_neg (by omega)]

/-- F1 (6.6)：所有低于 2N 次的系数，来自实际有理核。 -/
theorem even_G_R_inverse_kernel {N : ℕ} (hN : 1 ≤ N) (i j : Fin (2*N)) :
    (G (2*N)*R (2*N)*(G (2*N))⁻¹) i j =
      -(PowerSeries.coeff ℚ[X] i.val (rationalKernel (2*N))).coeff j.val := by
  have hs : (-1:ℚ)^(2*N-1) = -1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [show 2*k.succ-1 = 2*k+1 by omega, pow_add, pow_mul]
    norm_num
  rw [G_R_inverse_apply, rationalKernel_coeff, pow_add, hs]
  split_ifs <;> ring

end CP.Series

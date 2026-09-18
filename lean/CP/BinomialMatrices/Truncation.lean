import CP.BinomialMatrices
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse

namespace CP.Series
open Polynomial Finset Matrix

/-- (1+X)^(-d) 的标准二项式形式幂级数；与目标矩阵无关地定义。 -/
noncomputable def negPower (A : Type*) [CommRing A] (d : ℕ) : PowerSeries A :=
  PowerSeries.binomialSeries A (-(d:ℤ))

@[simp] theorem negPower_zero (A : Type*) [CommRing A] : negPower A 0 = 1 := by
  simpa [negPower] using (PowerSeries.binomialSeries_nat (A := A) 0)

theorem negPower_add (A : Type*) [CommRing A] (d e : ℕ) :
    negPower A (d+e) = negPower A d*negPower A e := by
  simp [negPower, neg_add_rev, mul_comm]

theorem negPower_eq_pow (A : Type*) [CommRing A] (d : ℕ) :
    negPower A d = negPower A 1 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [negPower_add, ih, pow_succ]

theorem negPower_coeff (A : Type*) [CommRing A] (j i : ℕ) :
    PowerSeries.coeff A i (negPower A (j+1)) =
      (-1)^i*((i+j).choose i : A) := by
  rw [negPower, ← PowerSeries.rescale_neg_one_invOneSubPow,
    PowerSeries.coeff_rescale, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk]
  rw [Nat.add_comm j i, Nat.choose_symm_add]

theorem positive_power_coeff (A : Type*) [CommRing A] (d i : ℕ) :
    PowerSeries.coeff A i ((1+PowerSeries.X : PowerSeries A)^d) = (d.choose i : A) := by
  rw [← PowerSeries.binomialSeries_nat, PowerSeries.binomialSeries_coeff,
    Ring.choose_natCast]
  simp

theorem negPower_cancel (A : Type*) [CommRing A] (d e : ℕ) :
    (1+PowerSeries.X : PowerSeries A)^(d+e)*negPower A e =
      (1+PowerSeries.X)^d := by
  rw [← PowerSeries.binomialSeries_nat, negPower, ← PowerSeries.binomialSeries_add]
  have he : ((d+e : ℕ):ℤ) + -(e:ℤ) = d := by omega
  rw [he, PowerSeries.binomialSeries_nat]

theorem negPower_one_inverse (A : Type*) [CommRing A] :
    (1+PowerSeries.X : PowerSeries A)*negPower A 1 = 1 := by
  simpa using negPower_cancel A 0 1

/-- 任意有限向量所代表的实际多项式。 -/
noncomputable def vectorPolynomial {q : ℕ} (v : Fin q → ℚ) : ℚ[X] :=
  ∑ j : Fin q, Polynomial.C (v j)*Polynomial.X^j.val

/-- (6.4) 右端的实际 Möbius 代换，尚未截断。 -/
noncomputable def transformed {q : ℕ} (v : Fin q → ℚ) : PowerSeries ℚ :=
  negPower ℚ 1 * (vectorPolynomial v).eval₂ (PowerSeries.C ℚ) (-negPower ℚ 1)

theorem transformed_expansion {q : ℕ} (v : Fin q → ℚ) :
    transformed v = ∑ j : Fin q,
      PowerSeries.C ℚ ((-1)^j.val*v j)*negPower ℚ (j.val+1) := by
  unfold transformed vectorPolynomial
  simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [negPower_eq_pow ℚ (j.val+1), pow_succ, neg_pow]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- (6.4) 的逐系数有限接口，对每个 i<q 成立。 -/
theorem G_mulVec_coeff {q : ℕ} (v : Fin q → ℚ) (i : Fin q) :
    (G q *ᵥ v) i = PowerSeries.coeff ℚ i.val (transformed v) := by
  rw [transformed_expansion]
  simp only [Matrix.mulVec, dotProduct, map_sum, PowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [negPower_coeff]
  unfold G
  rw [pow_add]
  ring

end CP.Series

namespace CP.Series
open Polynomial Finset Matrix

theorem signed_vandermonde (a j i : ℕ) (ha : j+1 ≤ a) :
    (∑ k ∈ range (i+1), (-1:ℚ)^k*(a.choose (i-k):ℚ)*((k+j).choose k:ℚ)) =
      ((a-(j+1)).choose i : ℚ) := by
  have he := negPower_cancel ℚ (a-(j+1)) (j+1)
  rw [Nat.sub_add_cancel ha, mul_comm] at he
  have hc := congrArg (PowerSeries.coeff ℚ i) he
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [negPower_coeff, positive_power_coeff, Nat.succ_eq_add_one] at hc
  rw [← hc]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem sum_fin_le {q : ℕ} (i : Fin q) (f : ℕ → ℚ) :
    (∑ k : Fin q, if k.val ≤ i.val then f k.val else 0) =
      ∑ k ∈ range (i.val+1), f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ i.val then f k else 0) q]
  calc
    _ = ∑ k ∈ range (i.val+1), if k ≤ i.val then f k else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by have := i.isLt; omega))
      intro k hk hk'
      simp only [mem_range] at hk hk'
      simp [show ¬k ≤ i.val by omega]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (show k ≤ i.val by have := mem_range.mp hk; omega)]

/-- (6.5) 右端的显式有限下三角矩阵。 -/
def conjugateCandidate (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  fun i j => if j.val ≤ i.val then (-1)^(q-1+i.val)*((q+i.val).choose (i.val-j.val):ℚ) else 0

theorem conjugateCandidate_mul_G (q : ℕ) :
    conjugateCandidate q * G q = G q * R q := by
  ext i j
  rw [Matrix.mul_apply, mul_R_apply]
  have hs (k : Fin q) : conjugateCandidate q i k * G q k j =
      (-1:ℚ)^(q-1+i.val+j.val) *
        (if k.val ≤ i.val then (-1:ℚ)^k.val*((q+i.val).choose (i.val-k.val):ℚ)*
          ((k.val+j.val).choose k.val:ℚ) else 0) := by
    by_cases hk : k.val ≤ i.val
    · simp only [conjugateCandidate, if_pos hk, G, pow_add]
      ring
    · simp [conjugateCandidate, hk]
  simp_rw [hs]
  rw [← Finset.mul_sum, sum_fin_le i (fun k => (-1:ℚ)^k *
    ((q+i.val).choose (i.val-k):ℚ)*((k+j.val).choose k:ℚ)),
    signed_vandermonde _ _ _ (by have := j.isLt; omega)]
  have he : q-1+i.val+j.val = i.val+j.rev.val+2*j.val := by
    rw [Fin.val_rev]
    have := j.isLt
    omega
  have hb : q+i.val-(j.val+1) = i.val+j.rev.val := by
    rw [Fin.val_rev]
    have := j.isLt
    omega
  rw [he, hb, pow_add, pow_mul]
  norm_num
  rfl

/-- F1 (6.5)：一般有限 q 的显式共轭式。 -/
theorem G_R_inverse (q : ℕ) : G q * R q * (G q)⁻¹ = conjugateCandidate q := by
  have hu : IsUnit (G q).det := by rw [det_G]; exact isUnit_one
  calc
    _ = (conjugateCandidate q*G q)*(G q)⁻¹ := by rw [conjugateCandidate_mul_G]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem G_R_inverse_apply (q : ℕ) (i j : Fin q) :
    (G q*R q*(G q)⁻¹) i j =
      if j.val ≤ i.val then (-1)^(q-1+i.val)*((q+i.val).choose (i.val-j.val):ℚ) else 0 := by
  rw [G_R_inverse]
  rfl

end CP.Series

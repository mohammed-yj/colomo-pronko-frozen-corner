import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace CP
open Matrix Polynomial Finset

/-- All matrices are finite, with the manuscript's zero-based indices. -/
def T (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  fun i j => (-1) ^ (j : ℕ) * (i.val.choose j.val : ℚ)

def G (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  fun i j => (-1) ^ (i.val + j.val) * ((i.val + j.val).choose i.val : ℚ)

def U (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  fun i j => if i ≤ j then (-1) ^ (j.val - i.val) *
    ((q - 1 - i.val).choose (j.val - i.val) : ℚ) else 0

/-- Reversal is the explicit finite involution Fin.rev. -/
def R (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  fun i j => if i.rev = j then 1 else 0

def B (q : ℕ) : Matrix (Fin q) (Fin q) ℚ := R q * U q

def K (q : ℕ) : Matrix (Fin q) (Fin q) ℚ := fun i j =>
  ((i.val + j.val).choose i.val : ℚ) +
  (-1) ^ i.val * (j.val.choose i.val : ℚ) -
  (-1) ^ j.val * (i.val.choose j.val : ℚ)

def tailDiagonal (q s : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  Matrix.diagonal fun i => if q - s ≤ i.val then 1 else 0

@[simp] theorem R_mul_apply {q r : ℕ} (A : Matrix (Fin q) (Fin r) ℚ)
    (i : Fin q) (j : Fin r) : (R q * A) i j = A i.rev j := by
  simp [R, Matrix.mul_apply]

@[simp] theorem mul_R_apply {q r : ℕ} (A : Matrix (Fin r) (Fin q) ℚ)
    (i : Fin r) (j : Fin q) : (A * R q) i j = A i j.rev := by
  have he : ∀ k : Fin q, k.rev = j ↔ k = j.rev := by
    intro k
    constructor <;> intro h
    · simpa using congrArg Fin.rev h
    · rw [h]; simp
  simp [R, Matrix.mul_apply, he]

@[simp] theorem R_sq (q : ℕ) : R q * R q = 1 := by
  ext i j
  simp [R, Matrix.one_apply]

@[simp] theorem R_transpose (q : ℕ) : (R q)ᵀ = R q := by
  ext i j
  have : j.rev = i ↔ i.rev = j := by
    constructor <;> intro h
    · simpa using (congrArg Fin.rev h).symm
    · simpa using (congrArg Fin.rev h).symm
  simp [R, Matrix.transpose_apply, this]

@[simp] theorem U_diag {q : ℕ} (i : Fin q) : U q i i = 1 := by simp [U]

theorem U_below {q : ℕ} {i j : Fin q} (h : j < i) : U q i j = 0 := by
  simp [U, not_le.mpr h]

theorem T_above {q : ℕ} {i j : Fin q} (h : i < j) : T q i j = 0 := by
  simp [T, Nat.choose_eq_zero_of_lt h]

/-- A signed Pascal row is exactly the coefficients of (1-X)^i. -/
theorem coeff_one_sub_X_pow (i j : ℕ) :
    (((1 - X : ℚ[X]) ^ i).coeff j) = (-1 : ℚ) ^ j * (i.choose j : ℚ) := by
  have hp : ((1 + X : ℚ[X]) ^ i).comp (C (-1) * X) = (1 - X) ^ i := by
    simp [Polynomial.pow_comp, Polynomial.add_comp, sub_eq_add_neg]
  rw [← hp, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_one_add_X_pow]
  ring

/-- Exact finite expansion, with the bound checked before taking coefficients. -/
theorem signed_row_expansion {q : ℕ} (i : Fin q) :
    (1 - X : ℚ[X]) ^ i.val =
      ∑ k : Fin q, C (T q i k) * X ^ k.val := by
  have hd : ((1 - X : ℚ[X]) ^ i.val).natDegree < q := by
    calc
      _ ≤ i.val := by
        calc
          _ ≤ (1 - X : ℚ[X]).natDegree * i.val := by simpa [Nat.mul_comm] using (natDegree_pow_le (p := (1-X : ℚ[X])) (n := i.val))
          _ ≤ 1 * i.val := Nat.mul_le_mul_right _ (by compute_degree)
          _ = i.val := one_mul _
      _ < q := i.isLt
  rw [Polynomial.as_sum_range' _ q hd]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← C_mul_X_pow_eq_monomial, coeff_one_sub_X_pow]
  rfl

/-- Binomial inversion, for every finite order q, including q = 0. -/
theorem T_sq (q : ℕ) : T q * T q = 1 := by
  ext i j
  have hh := congrArg (fun p : ℚ[X] => (p.comp (1-X)).coeff j.val)
    (signed_row_expansion i)
  simp only [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.X_comp, sub_sub_cancel, Polynomial.sum_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.coeff_X_pow,
    Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul] at hh
  simp only [coeff_one_sub_X_pow] at hh
  simpa [Matrix.mul_apply, T, Matrix.one_apply, Fin.ext_iff, eq_comm] using hh.symm

/-- Vandermonde in the form required for finite Pascal Gram products. -/
theorem choose_gram_sum (i j q : ℕ) (hi : i < q) :
    ∑ k ∈ range q, (i.choose k : ℚ) * (j.choose k : ℚ) =
      ((i+j).choose i : ℚ) := by
  have hv := Nat.add_choose_eq j i i
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => j.choose ij.1 * i.choose ij.2) i] at hv
  have hv' : ∑ k ∈ range (i+1), (i.choose k : ℚ) * (j.choose k : ℚ) =
      ((i+j).choose i : ℚ) := by
    rw [Nat.add_comm] at hv
    have hh : ∑ k ∈ range (i+1), j.choose k * i.choose (i-k) =
        ∑ k ∈ range (i+1), i.choose k * j.choose k := by
      apply sum_congr rfl
      intro k hk
      rw [Nat.choose_symm (by simpa using Nat.le_of_lt_succ (mem_range.mp hk))]
      exact Nat.mul_comm _ _
    rw [hh] at hv
    exact_mod_cast hv.symm
  rw [← hv']
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hk'
  have hik : i < k := by simp only [mem_range] at hk hk'; omega
  simp [Nat.choose_eq_zero_of_lt hik]

/-- The unsigned Gram factorization used in (6.4). -/
theorem T_mul_transpose (q : ℕ) :
    T q * (T q)ᵀ = (fun i j => ((i.val + j.val).choose i.val : ℚ)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, T]
  have hs (k : Fin q) :
      (-1 : ℚ)^k.val * (i.val.choose k.val : ℚ) *
        ((-1 : ℚ)^k.val * (j.val.choose k.val : ℚ)) =
      (i.val.choose k.val : ℚ) * (j.val.choose k.val : ℚ) := by
    have hk : (-1 : ℚ)^k.val * (-1 : ℚ)^k.val = 1 := by
      rw [← mul_pow]; norm_num
    calc
      _ = ((-1 : ℚ)^k.val * (-1 : ℚ)^k.val) *
        ((i.val.choose k.val : ℚ) * (j.val.choose k.val : ℚ)) := by ring
      _ = _ := by rw [hk, one_mul]
  simp_rw [hs]
  rw [Fin.sum_univ_eq_sum_range (fun k => (i.val.choose k : ℚ) * (j.val.choose k : ℚ)) q]
  exact choose_gram_sum i.val j.val q i.isLt

/-- The first factorization in manuscript (6.4), with explicit K. -/
theorem K_sub_one (q : ℕ) : K q - 1 = (T q + 1) * ((T q)ᵀ - 1) := by
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    T_mul_transpose]
  ext i j
  simp [K, T, Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply]
  ring


/-- The sign diagonal, kept separate from the true kernel D_N. -/
def signDiagonal (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  Matrix.diagonal fun i => (-1)^i.val

theorem B_eq_signed_T_R (q : ℕ) : B q = signDiagonal q * T q * R q := by
  ext i j
  simp only [B, R_mul_apply, mul_R_apply, Matrix.diagonal_mul, signDiagonal, T]
  unfold U
  split_ifs with hij
  · have hc : q-1-i.rev.val = i.val := by simp [Fin.val_rev]; omega
    have hd : i.val-(j.val-i.rev.val) = j.rev.val := by simp [Fin.val_rev]; omega
    have hle : j.val-i.rev.val ≤ i.val := by simp only [Fin.le_def, Fin.val_rev] at *; omega
    rw [hc, ← Nat.choose_symm hle, hd]
    rw [← mul_assoc, ← pow_add]
    congr 1
    conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
    conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
    congr 1
    simp only [Fin.le_def, Fin.val_rev] at *
    omega
  · have hj : i.val < j.rev.val := by simp only [Fin.le_def, Fin.val_rev] at *; omega
    rw [Nat.choose_eq_zero_of_lt hj]
    simp

/-- The signed Gram factorization in F1. -/
theorem B_gram (q : ℕ) : B q * (B q)ᵀ = G q := by
  rw [B_eq_signed_T_R, Matrix.transpose_mul, Matrix.transpose_mul, R_transpose]
  have hrr := R_sq q
  have ht := T_mul_transpose q
  calc
    _ = signDiagonal q * (T q * (R q * R q) * (T q)ᵀ) * (signDiagonal q)ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = signDiagonal q * (T q * (T q)ᵀ) * (signDiagonal q)ᵀ := by rw [hrr]; simp
    _ = G q := by
      rw [ht]
      ext i j
      simp [signDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, G, pow_add]
      ring

theorem det_U (q : ℕ) : (U q).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [U_diag]
  · intro i j hij
    exact U_below hij

theorem det_G (q : ℕ) : (G q).det = 1 := by
  rw [← B_gram, Matrix.det_mul, Matrix.det_transpose, B, Matrix.det_mul, det_U,
    mul_one, ← Matrix.det_mul, R_sq, Matrix.det_one]

/-- The polynomial whose coefficient row is B. -/
noncomputable def bRow {q : ℕ} (i : Fin q) : ℚ[X] := X^i.rev.val * (1-X)^i.val

theorem bRow_coeff {q : ℕ} (i j : Fin q) : (bRow i).coeff j.val = B q i j := by
  simp only [bRow, Polynomial.coeff_X_pow_mul', coeff_one_sub_X_pow,
    B, R_mul_apply, U]
  have hc : q-1-i.rev.val = i.val := by simp [Fin.val_rev]; omega
  rw [hc]
  rfl

theorem bRow_expansion {q : ℕ} (i : Fin q) :
    bRow i = ∑ k : Fin q, C (B q i k) * X^k.val := by
  have hd : (bRow i).natDegree < q := by
    calc
      _ ≤ i.rev.val + i.val := by
        apply (Polynomial.natDegree_mul_le).trans
        apply Nat.add_le_add
        · simp
        · calc
            _ ≤ (1-X : ℚ[X]).natDegree * i.val := by simpa [Nat.mul_comm] using (natDegree_pow_le (p := (1-X : ℚ[X])) (n := i.val))
            _ ≤ 1*i.val := Nat.mul_le_mul_right _ (by compute_degree)
            _ = i.val := one_mul _
      _ < q := by simp [Fin.val_rev]; omega
  rw [Polynomial.as_sum_range' _ q hd, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro k _
  rw [← C_mul_X_pow_eq_monomial, bRow_coeff]

theorem B_mul_T (q : ℕ) : B q * T q = R q * B q := by
  ext i j
  have hp : (bRow i).comp (1-X) = bRow i.rev := by
    simp [bRow, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp,
      Polynomial.X_comp, mul_comm]
  have hh := congrArg (fun p : ℚ[X] => (p.comp (1-X)).coeff j.val) (bRow_expansion i)
  dsimp only at hh
  rw [hp, bRow_coeff] at hh
  simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, coeff_one_sub_X_pow] at hh
  rw [R_mul_apply]
  simpa [Matrix.mul_apply, T] using hh.symm

/-- The second identity in (6.4), without assuming a Gram factorization. -/
theorem K_congruence (q : ℕ) :
    B q * (K q-1) * (B q)ᵀ = (R q+1)*G q*(R q-1) := by
  rw [K_sub_one]
  have hl : B q*(T q+1) = (R q+1)*B q := by
    simp [Matrix.mul_add, Matrix.add_mul, B_mul_T]
  have hr : ((T q)ᵀ-1)*(B q)ᵀ = (B q)ᵀ*(R q-1) := by
    have hh := congrArg Matrix.transpose (B_mul_T q)
    simp only [Matrix.transpose_mul, R_transpose] at hh
    simpa [Matrix.sub_mul, Matrix.mul_sub] using congrArg (fun A => A-(B q)ᵀ) hh
  calc
    _ = (B q*(T q+1))*(((T q)ᵀ-1)*(B q)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = ((R q+1)*B q)*((B q)ᵀ*(R q-1)) := by rw [hl,hr]
    _ = (R q+1)*(B q*(B q)ᵀ)*(R q-1) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [B_gram]


@[simp] theorem signDiagonal_sq (q : ℕ) : signDiagonal q*signDiagonal q = 1 := by
  ext i j
  simp only [signDiagonal, Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with hij
  · subst j
    rw [← mul_pow]
    norm_num
  · simp

@[simp] theorem signDiagonal_transpose (q : ℕ) : (signDiagonal q)ᵀ = signDiagonal q := by
  simp [signDiagonal]

theorem G_signed_factor (q : ℕ) :
    G q = signDiagonal q*T q*(T q)ᵀ*signDiagonal q := by
  rw [← B_gram, B_eq_signed_T_R, Matrix.transpose_mul, Matrix.transpose_mul,
    R_transpose, signDiagonal_transpose]
  calc
    _ = signDiagonal q*T q*(R q*R q)*(T q)ᵀ*signDiagonal q := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [R_sq]; simp

theorem G_inverse_factor (q : ℕ) :
    (G q)⁻¹ = signDiagonal q*(T q)ᵀ*T q*signDiagonal q := by
  apply Matrix.inv_eq_right_inv
  rw [G_signed_factor]
  have ht : (T q)ᵀ*(T q)ᵀ = 1 := by
    have hh := congrArg Matrix.transpose (T_sq q)
    simpa using hh
  calc
    _ = signDiagonal q*T q*(T q)ᵀ*(signDiagonal q*signDiagonal q)*
        (T q)ᵀ*T q*signDiagonal q := by simp only [Matrix.mul_assoc]
    _ = signDiagonal q*T q*((T q)ᵀ*(T q)ᵀ)*T q*signDiagonal q := by
      rw [signDiagonal_sq]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = signDiagonal q*(T q*T q)*signDiagonal q := by rw [ht]; simp [Matrix.mul_assoc]
    _ = 1 := by rw [T_sq]; simpa using signDiagonal_sq q

/-- The inverse coefficients are an explicitly bounded finite Gram sum.
This is the coefficient form of Σ_{k<q}(1+x)^k(1+y)^k. -/
theorem G_inverse_apply (q : ℕ) (i j : Fin q) :
    (G q)⁻¹ i j = ∑ k : Fin q, (k.val.choose i.val : ℚ)*(k.val.choose j.val : ℚ) := by
  rw [G_inverse_factor]
  rw [Matrix.mul_assoc (signDiagonal q) ((T q)ᵀ) (T q)]
  simp only [signDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, T]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hi : (-1 : ℚ)^i.val * (-1 : ℚ)^i.val = 1 := by rw [← mul_pow]; norm_num
  have hj : (-1 : ℚ)^j.val * (-1 : ℚ)^j.val = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℚ)^i.val * (-1 : ℚ)^i.val)*
        ((-1 : ℚ)^j.val * (-1 : ℚ)^j.val)*
        ((k.val.choose i.val : ℚ)*(k.val.choose j.val : ℚ)) := by ring
    _ = _ := by rw [hi,hj]; ring

end CP

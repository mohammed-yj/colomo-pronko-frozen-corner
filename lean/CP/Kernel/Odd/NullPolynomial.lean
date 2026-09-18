import CP.Kernel.Odd.KernelLift

namespace CP.Kernel
open Polynomial Matrix Finset

noncomputable def normalizedP (N : ℕ) : ℚ[X] := C ((b (N+1))⁻¹)*h (N+1)
noncomputable def shiftedP (N : ℕ) : ℚ[X] := (normalizedP N).comp (1+X)

/-- 规范 (4.15) 中的实际 ν 核。 -/
noncomputable def nuPolynomial (N : ℕ) : ℚ[X] :=
  C ((b (N+1)^2)⁻¹)*(h (N+1)).comp (1+X)*uStar N

noncomputable def nu (N : ℕ) : Fin (2*N+1) → ℚ := fun i => (nuPolynomial N).coeff i.val

theorem normalizedP_degree (N : ℕ) : (normalizedP N).natDegree ≤ N := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by have := h_natDegree_lt (N+1) (by omega); omega)

theorem shifted_h_degree (N : ℕ) : ((h (N+1)).comp (1+X)).natDegree ≤ N := by
  have hd : (1+X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  have hh : (h (N+1)).natDegree ≤ N := by have := h_natDegree_lt (N+1) (by omega); omega
  exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hh hd).trans (by omega))

theorem shiftedP_degree (N : ℕ) : (shiftedP N).natDegree ≤ N := by
  have hd : (1+X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul (normalizedP_degree N) hd).trans (by omega))

theorem uStar_eq_shift_reflect (N : ℕ) :
    uStar N = ((h (N+1)).comp (1+X)).reflect N := by
  have he := Polynomial.reflect_mul X ((h (N+1)).comp (1+X))
    (by simp : (X:ℚ[X]).natDegree ≤ 1) (shifted_h_degree N)
  have hx : (X : ℚ[X]).reflect 1 = 1 := by
    exact Polynomial.reflect_one_X
  rw [hx, one_mul] at he
  simpa only [uStar, u, Nat.add_comm] using he


theorem nuPolynomial_factor (N : ℕ) :
    nuPolynomial N = shiftedP N*(shiftedP N).reflect N := by
  rw [nuPolynomial, uStar_eq_shift_reflect]
  simp only [shiftedP, normalizedP, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.reflect_C_mul]
  rw [show (b (N+1)^2)⁻¹ = (b (N+1))⁻¹*(b (N+1))⁻¹ by simp only [pow_two, _root_.mul_inv_rev]]
  simp only [Polynomial.C_mul]
  ring

theorem nuPolynomial_degree (N : ℕ) : (nuPolynomial N).natDegree ≤ 2*N := by
  rw [nuPolynomial_factor]
  have he := Polynomial.natDegree_mul_le_of_le (shiftedP_degree N)
    (reflect_degree _ _ (shiftedP_degree N))
  omega

theorem nuPolynomial_reflect (N : ℕ) : (nuPolynomial N).reflect (2*N) = nuPolynomial N := by
  rw [nuPolynomial_factor, show 2*N = N+N by omega,
    Polynomial.reflect_mul _ _ (shiftedP_degree N) (reflect_degree _ _ (shiftedP_degree N)),
    reflect_twice, mul_comm]

theorem normalizedP_reflect (N : ℕ) : (normalizedP N).reflect N = normalizedP N := by
  ext i
  simp only [Polynomial.coeff_reflect, normalizedP, Polynomial.coeff_C_mul]
  by_cases hi : i ≤ N
  · rw [Polynomial.revAt_le hi]
    rw [show (h (N+1)).coeff (N-i) = (h (N+1)).coeff i by
      simpa only [Nat.add_sub_cancel] using h_coeff_palindrome (N+1) i (by omega) (by omega)]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)]

theorem nu_reversal (N : ℕ) : R (2*N+1) *ᵥ nu N = nu N := by
  funext i
  have he := congrArg (fun p : ℚ[X] => p.coeff i.val) (nuPolynomial_reflect N)
  simp only [Polynomial.coeff_reflect] at he
  rw [Polynomial.revAt_le (by have := i.isLt; omega)] at he
  have hrev : (2*N+1)-1-i.val = 2*N-i.val := by omega
  change (∑ j, (if i.rev = j then (1:ℚ) else 0)*(nuPolynomial N).coeff j.val) = _
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hev : i.rev.val = 2*N-i.val := by rw [Fin.val_rev]; omega
  change (nuPolynomial N).coeff i.rev.val = (nuPolynomial N).coeff i.val
  rw [hev]
  exact he

theorem normalizedP_eval_zero (N : ℕ) : (normalizedP N).eval 0 = 1 := by
  simp only [normalizedP, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  change (b (N+1))⁻¹*b (N+1) = 1
  exact inv_mul_cancel₀ (b_pos (N+1) (by omega)).ne'

theorem shiftedP_eval_neg_one (N : ℕ) : (shiftedP N).eval (-1) = 1 := by
  simp only [shiftedP, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, add_neg_cancel]
  exact normalizedP_eval_zero N

theorem nuPolynomial_eval_neg_one (N : ℕ) : (nuPolynomial N).eval (-1) = (-1)^N := by
  rw [nuPolynomial_factor, Polynomial.eval_mul, shiftedP_eval_neg_one,
    reflect_eval _ _ (shiftedP_degree N) (-1) (by norm_num)]
  norm_num [shiftedP_eval_neg_one]

/-- eᵀν 的非零值由规范多项式的求值给出。 -/
theorem alternating_dot_nu (N : ℕ) : alternating (2*N+1) ⬝ᵥ nu N = (-1)^N := by
  have he := Polynomial.eval₂_eq_sum_range' (RingHom.id ℚ)
    (p := nuPolynomial N) (n := 2*N+1) (by have := nuPolynomial_degree N; omega) (-1)
  rw [← Fin.sum_univ_eq_sum_range] at he
  have hv : (nuPolynomial N).eval (-1) =
      ∑ i : Fin (2*N+1), (nuPolynomial N).coeff i.val*(-1)^i.val := he
  rw [← nuPolynomial_eval_neg_one N, hv]
  unfold dotProduct alternating nu
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem alternating_dot_nu_ne_zero (N : ℕ) : alternating (2*N+1) ⬝ᵥ nu N ≠ 0 := by
  rw [alternating_dot_nu]
  exact pow_ne_zero _ (by norm_num)

end CP.Kernel

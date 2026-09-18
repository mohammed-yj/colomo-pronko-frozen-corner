import CP.Kernel.Univariate

namespace CP.Kernel
open Polynomial

section FieldTransport
variable {F : Type*} [Field F] (f : ℚ →+* F)

theorem reflect_eval₂ (p : ℚ[X]) (d : ℕ) (hp : p.natDegree ≤ d)
    (x : F) (hx : x ≠ 0) :
    (p.reflect d).eval₂ f x = x^d*p.eval₂ f x⁻¹ := by
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have he := Polynomial.eval₂_reflect_mul_pow f x⁻¹ d p hp
  simp only [invOf_eq_inv, inv_inv, inv_pow] at he
  have hh := congrArg (fun a : F => a*x^d) he
  simpa [mul_assoc, pow_ne_zero d hx, mul_comm] using hh

theorem sigmaPullback_eval₂ (d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d)
    (x : F) (hx : 1+x ≠ 0) :
    (sigmaPullback d p).eval₂ f x = (1+x)^d*p.eval₂ f (-1/(1+x)) := by
  have ht : -1-x ≠ 0 := by
    have he : -1-x = -(1+x) := by ring
    rw [he]
    exact neg_ne_zero.mpr hx
  simp only [sigmaPullback, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_comp, theta, Polynomial.eval₂_sub, Polynomial.eval₂_neg,
    Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_pow, map_pow, map_neg, map_one]
  rw [reflect_eval₂ f _ _ hp _ ht]
  have hi : (-1-x)⁻¹ = -1/(1+x) := by field_simp; ring
  rw [hi, ← mul_assoc, ← mul_pow, show (-1:F)*(-1-x) = 1+x by ring]

theorem sigma_u_eval₂ (N : ℕ) (x : F) (hx : 1+x ≠ 0) :
    (1+x)^(N+1)*(u N).eval₂ f (-1/(1+x)) = -(uStar N).eval₂ f x := by
  have he := congrArg (Polynomial.eval₂ f x) (sigma_u N)
  rw [sigmaPullback_eval₂ f _ _ (u_degree N) _ hx, Polynomial.eval₂_neg] at he
  exact he

theorem sigma_v_eval₂ {N : ℕ} (hN : 1 ≤ N) (x : F) (hx : 1+x ≠ 0) :
    (1+x)^(N+1)*(v N).eval₂ f (-1/(1+x)) = (vStar N).eval₂ f x := by
  have he := congrArg (Polynomial.eval₂ f x) (sigma_v hN)
  rw [sigmaPullback_eval₂ f _ _ (by have := v_degree hN; omega) _ hx] at he
  exact he

theorem sigma_uStar_eval₂ (N : ℕ) (x : F) (hx : 1+x ≠ 0) :
    (1+x)^(N+1)*(uStar N).eval₂ f (-1/(1+x)) =
      f (epsilon N)*(u N).eval₂ f (-1-x) := by
  have he := congrArg (Polynomial.eval₂ f x) (sigma_uStar N)
  rw [sigmaPullback_eval₂ f (N+1) (uStar N) (by exact reflect_degree _ _ (u_degree N)) _ hx] at he
  simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_comp,
    theta, Polynomial.eval₂_sub, Polynomial.eval₂_neg, Polynomial.eval₂_one,
    Polynomial.eval₂_X] using he

theorem sigma_vStar_eval₂ {N : ℕ} (hN : 1 ≤ N) (x : F) (hx : 1+x ≠ 0) :
    (1+x)^(N+1)*(vStar N).eval₂ f (-1/(1+x)) =
      f (epsilon N)*(v N).eval₂ f (-1-x) := by
  have he := congrArg (Polynomial.eval₂ f x) (sigma_vStar N)
  rw [sigmaPullback_eval₂ f (N+1) (vStar N) (by exact reflect_degree _ _ (by have := v_degree hN; omega)) _ hx] at he
  simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_comp,
    theta, Polynomial.eval₂_sub, Polynomial.eval₂_neg, Polynomial.eval₂_one,
    Polynomial.eval₂_X] using he

end FieldTransport
end CP.Kernel

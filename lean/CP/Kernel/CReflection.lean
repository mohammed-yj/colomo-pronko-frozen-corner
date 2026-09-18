import CP.Kernel.ActualC

namespace CP.Kernel
open Polynomial

noncomputable def alternant (N : ℕ) : Bivariate :=
  inX (u N)*inY (v N)-inX (v N)*inY (u N)
noncomputable def starAlternant (N : ℕ) : Bivariate :=
  inX (uStar N)*inY (vStar N)-inX (vStar N)*inY (uStar N)

theorem reflect_alternant (N : ℕ) :
    reflectXY (N+1) (alternant N) = starAlternant N := by
  simp only [alternant, starAlternant, reflectXY_sub, reflectXY_separated, uStar, vStar]

theorem reflect_starAlternant (N : ℕ) :
    reflectXY (N+1) (starAlternant N) = alternant N := by
  simp only [alternant, starAlternant, reflectXY_sub, reflectXY_separated,
    uStar, vStar, reflect_twice]

theorem alternant_degrees {N : ℕ} (hN : 1 ≤ N) :
    (alternant N).natDegree ≤ N+1 ∧ (starAlternant N).natDegree ≤ N+1 ∧
    (swapXY (alternant N)).natDegree ≤ N+1 ∧
    (swapXY (starAlternant N)).natDegree ≤ N+1 := by
  have hu := u_degree N
  have hv := (v_degree hN).trans (Nat.le_succ _)
  have hus : (uStar N).natDegree ≤ N+1 := reflect_degree _ _ hu
  have hvs : (vStar N).natDegree ≤ N+1 := reflect_degree _ _ hv
  have h1 := bracket_sub_degree (u N) (v N) (v N) (u N) (N+1) hu hv
  have h2 := bracket_sub_degree (uStar N) (vStar N) (vStar N) (uStar N) (N+1) hus hvs
  have hs1 : swapXY (alternant N) = -alternant N := by
    simp only [alternant, map_sub, map_mul, swap_inX, swap_inY]; ring
  have hs2 : swapXY (starAlternant N) = -starAlternant N := by
    simp only [starAlternant, map_sub, map_mul, swap_inX, swap_inY]; ring
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hs1, Polynomial.natDegree_neg]; exact h1
  · rw [hs2, Polynomial.natDegree_neg]; exact h2

theorem c_tail_reflect (q : ℕ) :
    reflectXY (q+2) (xx^q*(yy-xx)*(1+xx+xx*yy)) =
      -yy^q*(yy-xx)*(1+yy+xx*yy) := by
  have h0 : (yy-xx).natDegree ≤ 1 := by unfold xx yy; compute_degree
  have hs0 : (swapXY (yy-xx)).natDegree ≤ 1 := by
    rw [pair_factors_swap.1, Polynomial.natDegree_neg]; exact h0
  have h1 := pair_factor_degrees.1
  have hs1 : (swapXY (1+xx+xx*yy)).natDegree ≤ 1 := by
    rw [pair_factors_swap.2.1]; exact pair_factor_degrees.2
  have hp := Polynomial.natDegree_mul_le_of_le h0 h1
  have hsp : (swapXY ((yy-xx)*(1+xx+xx*yy))).natDegree ≤ 2 := by
    rw [map_mul]; exact Polynomial.natDegree_mul_le_of_le hs0 hs1
  have hx : (xx^q).natDegree ≤ q := by simp [xx]
  have hsx : (swapXY (xx^q)).natDegree ≤ q := by simp [yy]
  rw [mul_assoc, reflectXY_mul _ _ _ _ hx hp hsx hsp]
  have hm : reflectXY q (xx^q) = yy^q := by
    simpa [Polynomial.revAt] using reflectXY_monomial q q 0
  rw [hm,
    reflectXY_mul _ _ _ _ h0 h1 hs0 hs1,
    reflectXY_pair_factors.1, reflectXY_pair_factors.2.1]
  ring

theorem reflectXY_twice (d : ℕ) (p : Bivariate) :
    reflectXY d (reflectXY d p) = p := by
  ext i j
  simp only [reflectXY_coeff, Polynomial.revAt_invol]

theorem c_tail_reflect_second (q : ℕ) :
    reflectXY (q+2) (yy^q*(yy-xx)*(1+yy+xx*yy)) =
      -xx^q*(yy-xx)*(1+xx+xx*yy) := by
  have he := congrArg (reflectXY (q+2)) (c_tail_reflect q)
  rw [reflectXY_twice] at he
  have hn (p : Bivariate) : reflectXY (q+2) (-p) = -reflectXY (q+2) p := by
    ext i j
    simp only [reflectXY_coeff, Polynomial.coeff_neg]
  have he' : -yy^q*(yy-xx)*(1+yy+xx*yy) = -(yy^q*(yy-xx)*(1+yy+xx*yy)) := by ring
  rw [he', hn] at he
  linear_combination he

theorem cNumerator_reflection {N : ℕ} (hN : 1 ≤ N) :
    reflectXY (2*N+2) (cNumerator N) = cNumerator N := by
  have hn : cNumerator N = C (C ((b (N+1)^2)⁻¹))*(alternant N*starAlternant N) -
      xx^(2*N)*(yy-xx)*(1+xx+xx*yy) + yy^(2*N)*(yy-xx)*(1+yy+xx*yy) := by
    unfold cNumerator alternant starAlternant
    ring
  obtain ⟨h1,h2,h3,h4⟩ := alternant_degrees hN
  rw [hn, reflectXY_add, reflectXY_sub, reflectXY_scalar,
    c_tail_reflect, c_tail_reflect_second,
    show 2*N+2 = (N+1)+(N+1) by omega,
    reflectXY_mul _ _ _ _ h1 h2 h3 h4, reflect_alternant, reflect_starAlternant]
  ring

theorem cKernel_reflection {N : ℕ} (hN : 1 ≤ N) :
    reflectXY (2*N-1) (cKernel N) = -cKernel N := by
  apply mul_left_cancel₀ denominator_primitive.ne_zero
  have hdx : denominator.natDegree ≤ 3 := denominator_degree.le
  have hdy : (swapXY denominator).natDegree ≤ 3 := by
    rw [swap_denominator, Polynomial.natDegree_neg]; exact hdx
  have hr := reflectXY_mul denominator (cKernel N) 3 (2*N-1)
    hdx (cKernel_degree hN) hdy (swap_cKernel_degree hN)
  rw [show 3+(2*N-1) = 2*N+2 by omega, denominator_mul_cKernel hN,
    cNumerator_reflection hN, denominator_reflect] at hr
  linear_combination hr + denominator_mul_cKernel hN

theorem cMatrix_reflection {N : ℕ} (hN : 1 ≤ N) :
    R (2*N)*cMatrix N*R (2*N) = -cMatrix N := by
  ext i j
  have he := congrArg (fun p : Bivariate => (p.coeff i.val).coeff j.val)
    (cKernel_reflection hN)
  simp only [Polynomial.coeff_neg, reflectXY_coeff] at he
  rw [Polynomial.revAt_le (by have := i.isLt; omega),
    Polynomial.revAt_le (by have := j.isLt; omega)] at he
  simpa only [cMatrix, Matrix.neg_apply, mul_R_apply, R_mul_apply,
    Fin.val_rev, Nat.sub_sub, Nat.add_comm] using he

end CP.Kernel

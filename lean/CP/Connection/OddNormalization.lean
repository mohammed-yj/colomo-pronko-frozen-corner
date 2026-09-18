import CP.Connection.OddCandidate

namespace CP.Connection
open Matrix CP.Kernel Finset

noncomputable def oddCorrection (N : ℕ) : Matrix (Fin (N+1)) (Fin N) ℚ := fun i j =>
  if i=Fin.last N then 2*nu N (oddLeft N j)/nu N (oddCenter N) else 0

/-- (8.6) 未乘逆之前的一元行关系，由实际 νᵀΩ=0 得到。 -/
theorem oddZ_center_row (N : ℕ) :
    (fun j => oddZ N (Fin.last N) j) =
      -(fun i => 2*nu N (oddLeft N i)/nu N (oddCenter N)) ᵥ* oddX N := by
  funext j
  have hl := congrFun (nu_left_omega_zero N) (oddLeft N j)
  have hr := congrFun (nu_left_omega_zero N) (oddLeft N j).rev
  simp only [Matrix.vecMul,dotProduct,Pi.zero_apply] at hl hr
  rw [odd_sum] at hl hr
  have hx (i : Fin N) : omega (2*N+1) (oddLeft N i) (oddLeft N j)-
      omega (2*N+1) (oddLeft N i) (oddLeft N j).rev = oddX N i j := by
    simp only [omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,Fin.rev_rev,oddX]
    ring
  have hh : 2*(∑ i, nu N (oddLeft N i)*oddX N i j)+
      nu N (oddCenter N)*oddZ N (Fin.last N) j = 0 := by
    calc
      _ = ((∑ i, nu N (oddLeft N i)*omega (2*N+1) (oddLeft N i) (oddLeft N j))+
        (∑ i, nu N (oddLeft N i).rev*omega (2*N+1) (oddLeft N i).rev (oddLeft N j))+
        nu N (oddCenter N)*omega (2*N+1) (oddCenter N) (oddLeft N j))-
        ((∑ i, nu N (oddLeft N i)*omega (2*N+1) (oddLeft N i) (oddLeft N j).rev)+
        (∑ i, nu N (oddLeft N i).rev*omega (2*N+1) (oddLeft N i).rev (oddLeft N j).rev)+
        nu N (oddCenter N)*omega (2*N+1) (oddCenter N) (oddLeft N j).rev) := by
          simp only [nu_rev_apply]
          have he (i : Fin N) : omega (2*N+1) (oddLeft N i).rev (oddLeft N j) =
              -omega (2*N+1) (oddLeft N i) (oddLeft N j).rev := by
            simpa only [Fin.rev_rev] using omega_reflection_entry (2*N+1) (oddLeft N i) (oddLeft N j).rev
          simp only [he,omega_reflection_entry,oddZ,oddLower_center,Finset.mul_sum,
            ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
          rw [← sub_add_sub_comm]
          congr 1
          · rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← hx]
            ring
          · ring
      _ = 0 := by rw [hl,hr,sub_self]
  have hc : nu N (oddCenter N) ≠ 0 := (nu_center_pos N).ne'
  simp only [Matrix.neg_vecMul,Pi.neg_apply,Matrix.vecMul,dotProduct]
  have hs : (∑ i, 2*nu N (oddLeft N i)/nu N (oddCenter N)*oddX N i j) =
      2*(∑ i, nu N (oddLeft N i)*oddX N i j)/nu N (oddCenter N) := by
    simp only [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [neg_mul,Finset.sum_neg_distrib]
  rw [hs]
  apply (eq_neg_iff_add_eq_zero).mpr
  field_simp [hc]
  nlinarith [hh]

/-- (8.11)；底行的修正来自零向量，前 N 行来自真正的 XX⁻¹=I。 -/
theorem oddZ_mul_inverse {N : ℕ} (hN : 1 ≤ N) :
    oddZ N*(oddX N)⁻¹ = (oddE N)ᵀ-oddCorrection N := by
  have hx : oddX N*(oddX N)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (oddX_det_ne_zero hN).isUnit
  ext i j
  induction i using Fin.lastCases with
  | cast i =>
    have he := congrFun (congrFun hx i) j
    simp only [Matrix.mul_apply,oddZ_top] at he ⊢
    rw [he]
    simp [oddE,oddCorrection,Matrix.one_apply,eq_comm]
  | last =>
    have he := congrArg (fun v : Fin N → ℚ => v ᵥ* (oddX N)⁻¹) (oddZ_center_row N)
    dsimp only at he
    rw [Matrix.vecMul_vecMul,hx,Matrix.vecMul_one] at he
    have hj := congrFun he j
    change (∑ k, oddZ N (Fin.last N) k*(oddX N)⁻¹ k j) = _ at hj
    change (∑ k, oddZ N (Fin.last N) k*(oddX N)⁻¹ k j) = _
    rw [hj]
    simp [oddE,oddCorrection]

end CP.Connection

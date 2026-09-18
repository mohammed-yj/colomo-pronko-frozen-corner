import CP.Connection.OddFold

namespace CP.Connection
open Matrix CP.Kernel Finset

def oddPairEquiv (N : ℕ) : Fin (N+(N+1)) ≃ Fin (2*N+1) :=
  (pairedEquiv N (N+1)).trans (finCongr (by omega))

@[simp] theorem oddPair_left (N : ℕ) (i : Fin N) :
    oddPairEquiv N (Fin.castAdd (N+1) i) = oddLeft N i := by
  apply Fin.ext
  simp [oddPairEquiv,oddLeft]

@[simp] theorem oddPair_right (N : ℕ) (i : Fin N) :
    oddPairEquiv N (Fin.natAdd N i.castSucc) = (oddLeft N i).rev := by
  apply Fin.ext
  simp only [oddPairEquiv,Equiv.trans_apply,pairedEquiv_right,finCongr_apply,
    Fin.coe_cast,Fin.coe_natAdd,Fin.val_rev,Fin.coe_castSucc,oddLeft]
  have := i.isLt
  omega

@[simp] theorem oddPair_center (N : ℕ) :
    oddPairEquiv N (Fin.natAdd N (Fin.last N)) = oddCenter N := by
  apply Fin.ext
  simp only [oddPairEquiv,Equiv.trans_apply,pairedEquiv_right,finCongr_apply,
    Fin.coe_cast,Fin.coe_natAdd,Fin.val_rev,Fin.val_last,oddCenter]
  omega

/-- 有限指标精确拆成左部、反序右部和唯一中心。 -/
theorem odd_sum (N : ℕ) (f : Fin (2*N+1) → ℚ) :
    ∑ i, f i = (∑ i : Fin N, f (oddLeft N i))+
      (∑ i : Fin N, f (oddLeft N i).rev)+f (oddCenter N) := by
  rw [← Equiv.sum_comp (oddPairEquiv N) f,Fin.sum_univ_add,Fin.sum_univ_castSucc]
  simp only [oddPair_left,oddPair_right,oddPair_center]
  ring

theorem oddLeft_ne_center (N : ℕ) (i : Fin N) : oddLeft N i ≠ oddCenter N := by
  intro he
  have := congrArg Fin.val he
  simp only [oddLeft,oddCenter] at this
  have := i.isLt
  omega

theorem oddLeft_ne_rev (N : ℕ) (i j : Fin N) : oddLeft N i ≠ (oddLeft N j).rev := by
  intro he
  have := congrArg Fin.val he
  simp only [oddLeft,Fin.val_rev] at this
  have := i.isLt
  have := j.isLt
  omega

@[simp] theorem oddLeft_inj {N : ℕ} (i j : Fin N) : oddLeft N i = oddLeft N j ↔ i = j := by
  constructor
  · intro h; apply Fin.ext; exact congrArg (fun k : Fin (2*N+1) => k.val) h
  · exact congrArg (oddLeft N)

theorem centeredGammaOdd_reflect {N : ℕ} (hN : 1 ≤ N) (i j : Fin (2*N+1)) :
    centeredGammaOdd N i.rev j.rev = -centeredGammaOdd N i j := by
  have hg (i j : Fin (2*N+1)) : gammaOdd N i.rev j.rev = -gammaOdd N i j := by
    have he := congrFun (congrFun (gammaOdd_reflection hN) i) j
    simpa only [mul_R_apply,R_mul_apply,Matrix.neg_apply] using he
  have hcc : gammaOdd N (oddCenter N) (oddCenter N) = 0 := by
    have he := hg (oddCenter N) (oddCenter N)
    rw [oddCenter_rev] at he
    linarith
  change (centerProjection (oddCenter N) (nu N)*gammaOdd N*(centerProjection (oddCenter N) (nu N))ᵀ) i.rev j.rev = _
  rw [projected_entry _ _ _ hcc]
  change _ = -(centerProjection (oddCenter N) (nu N)*gammaOdd N*(centerProjection (oddCenter N) (nu N))ᵀ) i j
  rw [projected_entry _ _ _ hcc,hg,nu_rev_apply,nu_rev_apply]
  have hcj := hg (oddCenter N) j
  have hic := hg i (oddCenter N)
  rw [oddCenter_rev] at hcj hic
  rw [hcj,hic]
  ring

theorem centeredGammaOdd_center_row (N : ℕ) (j : Fin (2*N+1)) :
    centeredGammaOdd N (oddCenter N) j = 0 :=
  projected_center_row (oddCenter N) (nu N) (nu_center_pos N).ne' (gammaOdd N) j

noncomputable def oddX (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun i j =>
  G (2*N+1) (oddLeft N i).rev (oddLeft N j).rev-G (2*N+1) (oddLeft N i) (oddLeft N j)+
  G (2*N+1) (oddLeft N i) (oddLeft N j).rev-G (2*N+1) (oddLeft N i).rev (oddLeft N j)

noncomputable def oddXi (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun i j =>
  centeredGammaOdd N (oddLeft N i) (oddLeft N j)+
    centeredGammaOdd N (oddLeft N i) (oddLeft N j).rev

/-- (8.8) 的真正右逆来自完整中心投影乘积和精确有限求和。 -/
theorem odd_fold_right_inverse {N : ℕ} (hN : 1 ≤ N) : oddX N*oddXi N = 1 := by
  have hp := centered_product (oddCenter N) (nu N)
    (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N))
    (nu_center_pos N).ne' (omega (2*N+1)) (gammaOdd N) (omega_nu_zero N) (omega_gammaOdd hN)
  change omega (2*N+1)*centeredGammaOdd N = _ at hp
  ext i j
  have hl := congrFun (congrFun hp (oddLeft N i)) (oddLeft N j)
  have hr := congrFun (congrFun hp (oddLeft N i)) (oddLeft N j).rev
  simp only [Matrix.mul_apply,Matrix.sub_apply,Matrix.one_apply,Matrix.vecMulVec_apply,
    Pi.single_apply,oddLeft_inj,if_neg (oddLeft_ne_center N i),zero_mul,sub_zero,
    if_neg (oddLeft_ne_rev N i j)] at hl hr
  rw [odd_sum] at hl hr
  simp only [centeredGammaOdd_center_row,mul_zero,add_zero] at hl hr
  have hrev (k : Fin N) : centeredGammaOdd N (oddLeft N k).rev (oddLeft N j)+
      centeredGammaOdd N (oddLeft N k).rev (oddLeft N j).rev = -oddXi N k j := by
    rw [centeredGammaOdd_reflect hN]
    have he := centeredGammaOdd_reflect hN (oddLeft N k) (oddLeft N j).rev
    rw [Fin.rev_rev] at he
    rw [he]
    unfold oddXi
    ring
  have hx (k : Fin N) : omega (2*N+1) (oddLeft N i) (oddLeft N k)-
      omega (2*N+1) (oddLeft N i) (oddLeft N k).rev = oddX N i k := by
    simp only [omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,Fin.rev_rev,oddX]
    ring
  change (∑ k, oddX N i k*oddXi N k j) = if i=j then 1 else 0
  calc
    _ = ((∑ k, omega (2*N+1) (oddLeft N i) (oddLeft N k)*centeredGammaOdd N (oddLeft N k) (oddLeft N j))+
      (∑ k, omega (2*N+1) (oddLeft N i) (oddLeft N k).rev*centeredGammaOdd N (oddLeft N k).rev (oddLeft N j)))+
      ((∑ k, omega (2*N+1) (oddLeft N i) (oddLeft N k)*centeredGammaOdd N (oddLeft N k) (oddLeft N j).rev)+
      (∑ k, omega (2*N+1) (oddLeft N i) (oddLeft N k).rev*centeredGammaOdd N (oddLeft N k).rev (oddLeft N j).rev)) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hx]
        have he := hrev k
        unfold oddXi at he ⊢
        linear_combination -omega (2*N+1) (oddLeft N i) (oddLeft N k).rev*he
    _ = _ := by rw [hl,hr,add_zero]

theorem odd_fold_inverse {N : ℕ} (hN : 1 ≤ N) : (oddX N)⁻¹ = oddXi N :=
  Matrix.inv_eq_right_inv (odd_fold_right_inverse hN)

theorem oddX_det_ne_zero {N : ℕ} (hN : 1 ≤ N) : (oddX N).det ≠ 0 :=
  det_ne_zero_from_right_inverse _ _ (odd_fold_right_inverse hN)

noncomputable def freeOddS (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun i j =>
  -(centerProjection (oddCenter N) (nu N)*jMatrix (2*N+1)*(centerProjection (oddCenter N) (nu N))ᵀ)
    (oddLeft N i) (oddLeft N j)-
  (centerProjection (oddCenter N) (nu N)*jMatrix (2*N+1)*(centerProjection (oddCenter N) (nu N))ᵀ)
    (oddLeft N i) (oddLeft N j).rev

/-- (8.8)，对实际 J 与 O 做同一中心投影和折叠。 -/
theorem trueOddS_eq_free_add_inverse {N : ℕ} (hN : 1 ≤ N) :
    trueOddS N = freeOddS N+(oddX N)⁻¹ := by
  rw [odd_fold_inverse hN]
  ext i j
  rw [Matrix.add_apply,trueOddS_projected_fold hN]
  unfold freeOddS oddXi centeredGammaOdd gammaOdd projectedOddKernel
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_apply]
  unfold oddCenter
  ring

end CP.Connection

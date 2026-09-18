import CP.Connection.OddInverseFold

namespace CP.Connection
open Matrix CP.Kernel Finset
set_option maxHeartbeats 2000000

def oddLower (N : ℕ) (i : Fin (N+1)) : Fin (2*N+1) := oddPairEquiv N (Fin.natAdd N i)
@[simp] theorem oddLower_left (N : ℕ) (i : Fin N) : oddLower N i.castSucc = (oddLeft N i).rev := oddPair_right N i
@[simp] theorem oddLower_center (N : ℕ) : oddLower N (Fin.last N) = oddCenter N := oddPair_center N

def oddE (N : ℕ) : Matrix (Fin N) (Fin (N+1)) ℚ := fun i j => if i.castSucc=j then 1 else 0

@[simp] theorem oddE_mul_apply {N r : ℕ} (A : Matrix (Fin (N+1)) (Fin r) ℚ) (i : Fin N) (j : Fin r) :
    (oddE N*A) i j = A i.castSucc j := by simp [oddE,Matrix.mul_apply]
@[simp] theorem mul_oddE_castSucc {N r : ℕ} (A : Matrix (Fin r) (Fin N) ℚ) (i : Fin r) (j : Fin N) :
    (A*oddE N) i j.castSucc = A i j := by simp [oddE,Matrix.mul_apply]
@[simp] theorem mul_oddE_last {N r : ℕ} (A : Matrix (Fin r) (Fin N) ℚ) (i : Fin r) :
    (A*oddE N) i (Fin.last N) = 0 := by simp [oddE,Matrix.mul_apply]

noncomputable def oddZ (N : ℕ) : Matrix (Fin (N+1)) (Fin N) ℚ := fun i j =>
  omega (2*N+1) (oddLower N i) (oddLeft N j)-omega (2*N+1) (oddLower N i) (oddLeft N j).rev

theorem omega_reflection_entry (q : ℕ) (i j : Fin q) : omega q i.rev j.rev = -omega q i j := by
  simp only [omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,Fin.rev_rev]
  ring

@[simp] theorem oddZ_top (N : ℕ) (i j : Fin N) : oddZ N i.castSucc j = oddX N i j := by
  simp only [oddZ,oddLower_left,omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,Fin.rev_rev,oddX]
  ring

/-- 候选合同的交换子形式，使中央列的零项显式可见。 -/
theorem base_core_entry (q : ℕ) (i j : Fin q) :
    ((R q+1)*G q*(R q-1)) i j = omega q i j-omega q i j.rev := by
  simp only [Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,
    Matrix.add_apply,Matrix.sub_apply,mul_R_apply,R_mul_apply,omega,Fin.rev_rev]
  ring

theorem odd_omega_coordinate (N : ℕ) (i j : Fin (N+(N+1))) :
    omega (N+(N+1)) (pairedEquiv N (N+1) i) (pairedEquiv N (N+1) j) =
      omega (2*N+1) (oddPairEquiv N i) (oddPairEquiv N j) := by
  simp only [omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,G,oddPairEquiv,
    Equiv.trans_apply,finCongr_apply,Fin.coe_cast,Fin.val_rev]
  have hd (a : ℕ) : N+(N+1)-a=2*N+1-a := by omega
  simp only [hd]

theorem oddPair_rev (N : ℕ) (j : Fin (N+(N+1))) :
    (finCongr (show N+(N+1)=2*N+1 by omega)) ((pairedEquiv N (N+1) j).rev) =
      (oddPairEquiv N j).rev := by
  apply Fin.ext
  simp only [finCongr_apply,Fin.coe_cast,Fin.val_rev,oddPairEquiv,Equiv.trans_apply]
  omega

/-- (8.9) 中四个块的实际识别；中心列由 R 的不动点给出。 -/
theorem odd_baseL_congruence (N : ℕ) :
    connectionB N (N+1)*tailFirst (m:=N) (n:=N+1) (baseL N (N+1))*(connectionB N (N+1))ᵀ =
      blocks (oddX N) (-(oddX N*oddE N)) (oddZ N) (H N (N+1)-oddZ N*oddE N) := by
  rw [baseL_congruence]
  have hc : (paired (m:=N) (n:=N+1) (R (N+(N+1)))+1)*paired (G (N+(N+1)))*
      (paired (R (N+(N+1)))-1) =
      blocks (oddX N) (-(oddX N*oddE N)) (oddZ N) (-oddZ N*oddE N) := by
    rw [← paired_one N (N+1),← paired_add,← paired_sub,← paired_mul,← paired_mul]
    have hn (i j : Fin (N+(N+1))) :
        (paired (m:=N) (n:=N+1) ((R (N+(N+1))+1)*G (N+(N+1))*(R (N+(N+1))-1))) i j =
          omega (2*N+1) (oddPairEquiv N i) (oddPairEquiv N j)-
          omega (2*N+1) (oddPairEquiv N i) (oddPairEquiv N j).rev := by
      simp only [paired,Matrix.submatrix_apply,base_core_entry]
      rw [odd_omega_coordinate]
      congr 1
      simp only [omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,G,Fin.rev_rev,oddPairEquiv,
        Equiv.trans_apply,finCongr_apply,Fin.coe_cast,Fin.val_rev]
      have hd (a : ℕ) : N+(N+1)-a=2*N+1-a := by omega
      simp only [hd]
    ext i j
    rw [hn]
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · simp only [oddPair_left,blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁,omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,oddX,Fin.rev_rev]
      ring
    · rename_i i j
      induction j using Fin.lastCases with
      | last => simp only [oddPair_left,oddPair_center,oddCenter_rev,sub_self,blocks,Matrix.submatrix_apply,
          finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₁₂,
          Matrix.neg_apply,mul_oddE_last,neg_zero]
      | cast j =>
        simp only [oddPair_left,oddPair_right,Fin.rev_rev,blocks,Matrix.submatrix_apply,
          finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₁₂,
          Matrix.neg_apply,mul_oddE_castSucc,omega,Matrix.sub_apply,mul_R_apply,R_mul_apply,oddX,Fin.rev_rev]
        ring
    · simp only [oddPair_left,blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₂₁,oddZ,oddLower]
    · rename_i i j
      induction j using Fin.lastCases with
      | last => simp only [oddPair_center,oddCenter_rev,sub_self,blocks,Matrix.submatrix_apply,
          finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₂₂,Matrix.neg_mul,
          Matrix.neg_apply,mul_oddE_last,neg_zero]
      | cast j =>
        simp only [oddPair_right,Fin.rev_rev,blocks,Matrix.submatrix_apply,
          finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₂₂,Matrix.neg_mul,Matrix.neg_apply,
          mul_oddE_castSucc,oddZ,oddLower]
        ring
  rw [hc,blocks_add]
  simp only [add_zero,Matrix.neg_mul]
  congr 1
  abel

noncomputable def oddEliminated (N : ℕ) :=
  blocks (oddX N) (-(oddX N*oddE N)) (oddZ N) (H N (N+1)-oddZ N*oddE N)
noncomputable def oddEliminatedInverse (N : ℕ) :=
  blocks ((oddX N)⁻¹-oddE N*(H N (N+1))⁻¹*oddZ N*(oddX N)⁻¹)
    (oddE N*(H N (N+1))⁻¹) (-(H N (N+1))⁻¹*oddZ N*(oddX N)⁻¹) ((H N (N+1))⁻¹)

theorem oddEliminated_right_inverse {N : ℕ} (hN : 1 ≤ N) :
    oddEliminated N*oddEliminatedInverse N = 1 := by
  simpa only [oddEliminated,oddEliminatedInverse,Matrix.neg_mul] using
    elimination_right_inverse (oddX N) (oddX N)⁻¹ (H N (N+1)) (H N (N+1))⁻¹ (oddE N) (oddZ N)
      (Matrix.mul_nonsing_inv _ (oddX_det_ne_zero hN).isUnit)
      (Matrix.mul_nonsing_inv _ (by rw [det_H]; exact isUnit_one))

theorem oddEliminated_inverse {N : ℕ} (hN : 1 ≤ N) :
    (oddEliminated N)⁻¹ = oddEliminatedInverse N :=
  Matrix.inv_eq_right_inv (oddEliminated_right_inverse hN)

end CP.Connection

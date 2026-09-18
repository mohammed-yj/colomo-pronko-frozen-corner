import CP.Connection.BinomialBlocks

namespace CP.Connection
open Matrix CP.Kernel

@[simp] theorem paired_add {m n : ℕ} (A B : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :
    paired (m:=m) (n:=n) (A+B) = paired A+paired B := rfl
@[simp] theorem paired_sub {m n : ℕ} (A B : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :
    paired (m:=m) (n:=n) (A-B) = paired A-paired B := rfl
@[simp] theorem paired_neg {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :
    paired (m:=m) (n:=n) (-A) = -paired A := rfl
@[simp] theorem paired_one (m n : ℕ) : paired (m:=m) (n:=n) 1 = 1 := by
  simp [paired, Matrix.submatrix_one_equiv]

theorem paired_even_right (N : ℕ) (i : Fin N) :
    pairedEquiv N N (Fin.natAdd N i) = (Fin.castAdd N i).rev := by
  rw [pairedEquiv_right]
  apply Fin.ext
  simp only [Fin.coe_natAdd, Fin.val_rev, Fin.coe_castAdd]
  have := i.isLt
  omega

theorem paired_R_even (N : ℕ) :
    paired (m:=N) (n:=N) (R (N+N)) = blocks 0 1 1 0 := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  all_goals
    simp only [paired, Matrix.submatrix_apply, pairedEquiv_left, paired_even_right,
      R, Fin.rev_rev, blocks, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply]
  · rename_i i j
    have he : (Fin.castAdd N i).rev ≠ Fin.castAdd N j := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_rev,Fin.coe_castAdd] at this
      have := i.isLt
      have := j.isLt
      omega
    rw [if_neg he]
  · simp only [Fin.rev_inj,Fin.castAdd_inj]
  · simp only [Fin.castAdd_inj]
  · rename_i i j
    have he : Fin.castAdd N i ≠ (Fin.castAdd N j).rev := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_rev,Fin.coe_castAdd] at this
      have := i.isLt
      have := j.isLt
      omega
    rw [if_neg he]

theorem paired_anti_blocks {N : ℕ} (Z : Matrix (Fin (N+N)) (Fin (N+N)) ℚ)
    (hZ : R (N+N)*Z*R (N+N) = -Z) :
    paired (m:=N) (n:=N) Z =
      blocks (LL (paired Z)) (LR (paired Z)) (-LR (paired Z)) (-LL (paired Z)) := by
  have he := congrArg (paired (m:=N) (n:=N)) hZ
  rw [paired_mul,paired_mul,paired_R_even,paired_neg] at he
  rw [← blocks_reconstruct (paired Z), blocks_mul, blocks_mul] at he
  simp only [Matrix.zero_mul,Matrix.mul_zero,Matrix.one_mul,Matrix.mul_one,zero_add,add_zero] at he
  have hll := congrArg (LL (m:=N) (n:=N)) he
  have hlr := congrArg (LR (m:=N) (n:=N)) he
  rw [LL_blocks] at hll
  rw [LR_blocks] at hlr
  change RR (paired Z) = -LL (blocks (LL (paired Z)) (LR (paired Z)) (RL (paired Z)) (RR (paired Z))) at hll
  change RL (paired Z) = -LR (blocks (LL (paired Z)) (LR (paired Z)) (RL (paired Z)) (RR (paired Z))) at hlr
  simp only [LL_blocks,LR_blocks] at hll hlr
  have ha : RR (paired Z) = -LL (paired Z) := hll
  have hb : RL (paired Z) = -LR (paired Z) := hlr
  calc
    _ = blocks (LL (paired Z)) (LR (paired Z)) (RL (paired Z)) (RR (paired Z)) := (blocks_reconstruct _).symm
    _ = _ := by rw [ha,hb]

noncomputable def evenC (N : ℕ) : Matrix (Fin (N+N)) (Fin (N+N)) ℚ :=
  kernelMatrix (N+N) (cKernel N)
noncomputable def evenGamma (N : ℕ) : Matrix (Fin (N+N)) (Fin (N+N)) ℚ :=
  jMatrix (N+N)-evenC N
noncomputable def trueD (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  -LL (paired (m:=N) (n:=N) (evenC N))-LR (paired (m:=N) (n:=N) (evenC N))
noncomputable def freeD (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  -LL (paired (m:=N) (n:=N) (jMatrix (N+N)))-LR (paired (m:=N) (n:=N) (jMatrix (N+N)))
noncomputable def evenX (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  RR (paired (m:=N) (n:=N) (G (N+N)))-LL (paired (m:=N) (n:=N) (G (N+N)))+
    LR (paired (m:=N) (n:=N) (G (N+N)))-RL (paired (m:=N) (n:=N) (G (N+N)))

theorem evenGamma_right_inverse {N : ℕ} (hN : 1 ≤ N) : omega (N+N)*evenGamma N = 1 := by
  let P (q : ℕ) := omega q*(jMatrix q-kernelMatrix q (cKernel N)) = 1
  have hp : P (2*N) := omega_mul_J_sub_C N hN
  exact (congrArg P (show 2*N = N+N by omega)).mp hp


theorem evenGamma_anti {N : ℕ} (hN : 1 ≤ N) :
    R (N+N)*evenGamma N*R (N+N) = -evenGamma N := by
  let P (q : ℕ) := R q*(jMatrix q-kernelMatrix q (cKernel N))*R q =
    -(jMatrix q-kernelMatrix q (cKernel N))
  have hp : P (2*N) := j_sub_c_reflection hN
  exact (congrArg P (show 2*N = N+N by omega)).mp hp


theorem paired_omega_blocks (N : ℕ) : paired (m:=N) (n:=N) (omega (N+N)) =
    blocks (LR (paired (G (N+N)))-RL (paired (G (N+N))))
      (LL (paired (G (N+N)))-RR (paired (G (N+N))))
      (RR (paired (G (N+N)))-LL (paired (G (N+N))))
      (RL (paired (G (N+N)))-LR (paired (G (N+N)))) := by
  rw [omega,paired_sub,paired_mul,paired_mul,paired_R_even]
  conv_lhs => rw [← blocks_reconstruct (paired (m:=N) (n:=N) (G (N+N)))]
  rw [blocks_mul,blocks_mul]
  simp only [Matrix.zero_mul,Matrix.mul_zero,Matrix.one_mul,Matrix.mul_one,zero_add,add_zero]
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [blocks,Matrix.sub_apply,-Fin.natAdd_eq_addNat]

/-- 折叠后的右逆由完整 ΩΓ=I 的两个实际块共同推出。 -/
theorem evenX_right_inverse {N : ℕ} (hN : 1 ≤ N) :
    evenX N*(LL (paired (m:=N) (n:=N) (evenGamma N))+LR (paired (evenGamma N))) = 1 := by
  have he := congrArg (paired (m:=N) (n:=N)) (evenGamma_right_inverse hN)
  rw [paired_mul,paired_one,paired_omega_blocks,paired_anti_blocks _ (evenGamma_anti hN),blocks_mul] at he
  have ha := congrArg (LL (m:=N) (n:=N)) he
  have hb := congrArg (LR (m:=N) (n:=N)) he
  simp only [LL_blocks,LR_blocks] at ha hb
  have h0 : LL (1 : Matrix (Fin (N+N)) (Fin (N+N)) ℚ) = 1 := by
    ext i j; simp [LL,Matrix.one_apply]
  have h1 : LR (1 : Matrix (Fin (N+N)) (Fin (N+N)) ℚ) = 0 := by
    ext i j
    have hn : Fin.castAdd N i ≠ Fin.natAdd N j := by
      intro he; have := congrArg Fin.val he
      simp only [Fin.coe_castAdd,Fin.coe_natAdd] at this
      have := i.isLt
      omega
    simp [LR,Matrix.one_apply,hn,-Fin.natAdd_eq_addNat]
  rw [h0] at ha
  rw [h1] at hb
  calc
    _ = ((LR (paired (G (N+N)))-RL (paired (G (N+N))))*LL (paired (evenGamma N))+
        (LL (paired (G (N+N)))-RR (paired (G (N+N))))*(-LR (paired (evenGamma N))))+
        ((LR (paired (G (N+N)))-RL (paired (G (N+N))))*LR (paired (evenGamma N))+
        (LL (paired (G (N+N)))-RR (paired (G (N+N))))*(-LL (paired (evenGamma N)))) := by
      unfold evenX
      noncomm_ring
    _ = 1 := by rw [ha,hb,add_zero]

theorem evenX_inverse {N : ℕ} (hN : 1 ≤ N) :
    (evenX N)⁻¹ = LL (paired (m:=N) (n:=N) (evenGamma N))+LR (paired (evenGamma N)) :=
  Matrix.inv_eq_right_inv (evenX_right_inverse hN)

theorem evenX_det_ne_zero {N : ℕ} (hN : 1 ≤ N) : (evenX N).det ≠ 0 :=
  det_ne_zero_from_right_inverse _ _ (evenX_right_inverse hN)

/-- (8.2) 中实际折叠核的连接，未把主块逆冒充主块的逆。 -/
theorem trueD_eq_freeD_add_inverse {N : ℕ} (hN : 1 ≤ N) :
    trueD N = freeD N+(evenX N)⁻¹ := by
  rw [evenX_inverse hN]
  unfold trueD freeD evenGamma
  simp only [paired_sub,LL,LR,Matrix.submatrix_sub,Pi.sub_apply]
  abel

end CP.Connection

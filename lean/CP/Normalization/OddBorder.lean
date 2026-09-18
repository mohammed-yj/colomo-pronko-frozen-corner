import CP.Normalization.DiagonalBridge

namespace CP.Connection
open Matrix CP.Kernel

noncomputable def oddA (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun i j =>
  -oMatrix N (oddLeft N i) (oddLeft N j)-oMatrix N (oddLeft N i) (oddLeft N j).rev
noncomputable def oddH (N : ℕ) : Matrix (Fin N) (Fin 1) ℚ := fun i _ =>
  oMatrix N (oddLeft N i) (oddCenter N)
noncomputable def oddV (N : ℕ) : Matrix (Fin 1) (Fin N) ℚ := fun _ j => -2*nu N (oddLeft N j)
noncomputable def oddAlpha (N : ℕ) : Matrix (Fin 1) (Fin 1) ℚ := fun _ _ => nu N (oddCenter N)

/-- 规范 (5.4) 的实际有边框核，全部索引是 Fin。 -/
noncomputable def trueE (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℚ :=
  blocks (oddA N) (oddH N) (oddV N) (oddAlpha N)

@[simp] theorem trueE_LL (N : ℕ) (i j : Fin N) : trueE N i.castSucc j.castSucc = oddA N i j := by
  change trueE N (Fin.castAdd 1 i) (Fin.castAdd 1 j) = _
  simp [trueE,blocks]
@[simp] theorem trueE_Lc (N : ℕ) (i : Fin N) : trueE N i.castSucc (Fin.last N) = oddH N i 0 := by
  change trueE N (Fin.castAdd 1 i) (Fin.natAdd N (0 : Fin 1)) = _
  simp only [trueE,blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₁₂]
@[simp] theorem trueE_cL (N : ℕ) (i : Fin N) : trueE N (Fin.last N) i.castSucc = oddV N 0 i := by
  change trueE N (Fin.natAdd N (0 : Fin 1)) (Fin.castAdd 1 i) = _
  simp only [trueE,blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₂₁]
@[simp] theorem trueE_cc (N : ℕ) : trueE N (Fin.last N) (Fin.last N) = nu N (oddCenter N) := by
  change trueE N (Fin.natAdd N (0 : Fin 1)) (Fin.natAdd N (0 : Fin 1)) = _
  simp only [trueE,blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₂₂,oddAlpha]

def borderTail (N s : ℕ) (hs : s ≤ N) : Fin (N-s+1) ↪ Fin (N+1) :=
  ⟨fun i => ⟨s+i.val,by have := i.isLt; omega⟩,by
    intro i j h
    apply Fin.ext
    have := congrArg (fun k : Fin (N+1) => k.val) h
    dsimp only at this
    omega⟩

@[simp] theorem borderTail_left (N s : ℕ) (hs : s ≤ N) (i : Fin (N-s)) :
    borderTail N s hs i.castSucc = (kernelTail N s hs i).castSucc := by rfl
@[simp] theorem borderTail_last (N s : ℕ) (hs : s ≤ N) :
    borderTail N s hs (Fin.last (N-s)) = Fin.last N := by
  apply Fin.ext
  simp only [borderTail,Function.Embedding.coeFn_mk,Fin.val_last]
  omega

/-- 任意尾主块保留同一中心标量 α，不让它依赖 s。 -/
theorem trueE_tail_blocks (N s : ℕ) (hs : s ≤ N) :
    (trueE N).submatrix (borderTail N s hs) (borderTail N s hs) =
      blocks ((oddA N).submatrix (kernelTail N s hs) (kernelTail N s hs))
        ((oddH N).submatrix (kernelTail N s hs) id)
        ((oddV N).submatrix id (kernelTail N s hs)) (oddAlpha N) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  all_goals
    simp only [Matrix.submatrix_apply,borderTail_left,borderTail_last,trueE_LL,trueE_Lc,trueE_cL,trueE_cc]
  · change _ = blocks _ _ _ _ (Fin.natAdd (N-s) (0 : Fin 1)) (Fin.natAdd (N-s) (0 : Fin 1))
    simp only [blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₂₂,oddAlpha]
  · rename_i j
    change _ = blocks _ _ _ _ (Fin.natAdd (N-s) (0 : Fin 1)) (Fin.castAdd 1 j)
    simp only [blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_castAdd,Matrix.fromBlocks_apply₂₁,id_eq]
  · rename_i i
    change _ = blocks _ _ _ _ (Fin.castAdd 1 i) (Fin.natAdd (N-s) (0 : Fin 1))
    simp only [blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_castAdd,Matrix.fromBlocks_apply₁₂,id_eq]
  · rename_i i j
    change _ = blocks _ _ _ _ (Fin.castAdd 1 i) (Fin.castAdd 1 j)
    simp only [blocks,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castAdd,Matrix.fromBlocks_apply₁₁]

@[simp] theorem det_oddAlpha (N : ℕ) : (oddAlpha N).det = nu N (oddCenter N) := by
  simp [oddAlpha,Matrix.det_fin_one]

theorem oddAlpha_inverse (N : ℕ) : (oddAlpha N)⁻¹ = fun _ _ => (nu N (oddCenter N))⁻¹ := by
  apply Matrix.inv_eq_right_inv
  ext i j
  have hc : nu N (oddCenter N) ≠ 0 := (nu_center_pos N).ne'
  simp [oddAlpha,Matrix.mul_apply,Matrix.one_apply,hc,Subsingleton.elim i j]

/-- 真核 ℰ 的所有尾主块的有限舒尔补，不调用普法夫式。 -/
theorem trueE_tail_det (N s : ℕ) (hs : s ≤ N) :
    ((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det =
      nu N (oddCenter N)*((trueOddS N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det := by
  letI : Invertible (oddAlpha N) := Matrix.invertibleOfIsUnitDet _
    (by rw [det_oddAlpha]; exact (nu_center_pos N).ne'.isUnit)
  rw [trueE_tail_blocks,blocks,Matrix.det_submatrix_equiv_self,Matrix.det_fromBlocks₂₂,
    Matrix.invOf_eq_nonsing_inv,det_oddAlpha,oddAlpha_inverse]
  congr 1
  congr 1
  ext i j
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.submatrix_apply,oddA,oddH,oddV,trueOddS,
    Fin.sum_univ_one,id_eq]
  ring

end CP.Connection

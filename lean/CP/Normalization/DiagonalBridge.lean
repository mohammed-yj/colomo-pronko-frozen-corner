import CP.Connection.OddConnection
import CP.FiniteBridge

namespace CP.Connection
open Matrix CP.Kernel Finset

def addedEmbedding (m n s : ℕ) : Fin (m-s) ↪ Fin (m+n) :=
  ⟨fun i => ⟨n+i.val,by have := i.isLt; omega⟩,by
    intro i j h
    apply Fin.ext
    have := congrArg (fun k : Fin (m+n) => k.val) h
    dsimp only at this
    omega⟩

def kernelTail (m s : ℕ) (hs : s ≤ m) : Fin (m-s) ↪ Fin m :=
  ⟨fun i => ⟨s+i.val,by have := i.isLt; omega⟩,by
    intro i j h
    apply Fin.ext
    have := congrArg (fun k : Fin m => k.val) h
    dsimp only at this
    omega⟩

/-- 选择矩阵加回的恰是 n,…,n+m-s-1；其余有限边界全部保留。 -/
theorem candidate_add_back (m n s : ℕ) (hs : s ≤ m) :
    K (m+n)-tailDiagonal (m+n) s =
      baseL m n+selection (addedEmbedding m n s)*(selection (addedEmbedding m n s))ᵀ := by
  have hsel (i j : Fin (m+n)) :
      (selection (addedEmbedding m n s)*(selection (addedEmbedding m n s))ᵀ) i j =
        if i=j then (if n ≤ i.val ∧ i.val < n+(m-s) then 1 else 0) else 0 := by
    by_cases hi : n ≤ i.val ∧ i.val < n+(m-s)
    · let k : Fin (m-s) := ⟨i.val-n,by omega⟩
      have hk : i = addedEmbedding m n s k := by apply Fin.ext; dsimp [addedEmbedding,k]; omega
      have he : ∀ l : Fin (m-s), i = addedEmbedding m n s l ↔ l=k := by
        intro l
        rw [hk,(addedEmbedding m n s).injective.eq_iff]
        exact eq_comm
      simp only [Matrix.mul_apply,selection,Matrix.transpose_apply,he]
      simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true,hi]
      simp only [hk,eq_comm]
      simp
    · have he (l : Fin (m-s)) : i ≠ addedEmbedding m n s l := by
        intro h
        have hv := congrArg (fun k : Fin (m+n) => k.val) h
        have := l.isLt
        dsimp [addedEmbedding] at hv
        omega
      simp [Matrix.mul_apply,selection,he,hi]
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,baseL,tailDiagonal,Matrix.diagonal_apply,hsel]
  by_cases hij : i=j
  · subst j
    simp only [if_true]
    split_ifs <;> (try omega) <;> ring
  · simp [hij]

/-- 反序的前主块正是原核的尾主块，行列同时反序。 -/
theorem reversed_front_det (m s : ℕ) (hs : s ≤ m) (D : Matrix (Fin m) (Fin m) ℚ) :
    ((R m*D*R m).submatrix (frontEmbedding (Nat.sub_le m s)) (frontEmbedding (Nat.sub_le m s))).det =
      (D.submatrix (kernelTail m s hs) (kernelTail m s hs)).det := by
  have he (i : Fin (m-s)) : (frontEmbedding (Nat.sub_le m s) i).rev = kernelTail m s hs i.rev := by
    apply Fin.ext
    simp only [Fin.val_rev,frontEmbedding,kernelTail,Function.Embedding.coeFn_mk]
    have := i.isLt
    omega
  have hm : (R m*D*R m).submatrix (frontEmbedding (Nat.sub_le m s)) (frontEmbedding (Nat.sub_le m s)) =
      (D.submatrix (kernelTail m s hs) (kernelTail m s hs)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply,mul_R_apply,R_mul_apply,he,Fin.revPerm_apply]
  rw [hm,Matrix.det_submatrix_equiv_self]

/-- N2 的有限代数接口；随后对真实偶数/奇数核分别实例化。 -/
theorem candidate_tail_det {m n : ℕ} (D : Matrix (Fin m) (Fin m) ℚ)
    (hL : (baseL m n).det ≠ 0)
    (hc : 1+LL (tailFirst (m:=m) (n:=n) ((baseL m n)⁻¹)) =
      (U m)ᵀ*R m*D*R m*U m)
    (s : ℕ) (hs : s ≤ m) :
    (K (m+n)-tailDiagonal (m+n) s).det =
      (baseL m n).det*(D.submatrix (kernelTail m s hs) (kernelTail m s hs)).det := by
  rw [candidate_add_back m n s hs,det_diagonal_add_back _ _ hL]
  congr 1
  have he := congrArg (fun A : Matrix (Fin m) (Fin m) ℚ =>
    A.submatrix (frontEmbedding (Nat.sub_le m s)) (frontEmbedding (Nat.sub_le m s))) hc
  have ht (i : Fin (m-s)) :
      tailFirstEquiv m n (Fin.castAdd n (frontEmbedding (Nat.sub_le m s) i)) = addedEmbedding m n s i := by
    apply Fin.ext
    rw [tailFirstEquiv_left_val]
    rfl
  have ho : (1 : Matrix (Fin m) (Fin m) ℚ).submatrix
      (frontEmbedding (Nat.sub_le m s)) (frontEmbedding (Nat.sub_le m s)) = 1 := by
    ext i j
    simp [Matrix.one_apply,(frontEmbedding (Nat.sub_le m s)).injective.eq_iff]
  dsimp only at he
  simp only [Matrix.submatrix_add,Pi.add_apply] at he
  rw [ho] at he
  simp only [LL,tailFirst,Matrix.submatrix_submatrix,Function.comp_def,ht] at he
  rw [he]
  have hm : (U m)ᵀ*R m*D*R m*U m = (U m)ᵀ*(R m*D*R m)*U m := by
    simp only [Matrix.mul_assoc]
  rw [hm,det_front_congruence (Nat.sub_le m s) (U m) (R m*D*R m)
    (fun _ _ h => U_below h) (fun _ => U_diag _),reversed_front_det m s hs]

/-- 全部允许 s 的偶数有限桥；尚未引入任何枚举归一化。 -/
theorem even_finite_bridge (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s ≤ N) :
    (K (N+N)-tailDiagonal (N+N) s).det = (baseL N N).det*
      ((trueD N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det :=
  candidate_tail_det (trueD N) (even_baseL_det_ne_zero hN) (even_connection hN) s hs

/-- 全部允许 s 的奇数有限桥，核是实际中心舒尔补。 -/
theorem odd_finite_bridge (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s ≤ N) :
    (K (N+(N+1))-tailDiagonal (N+(N+1)) s).det = (baseL N (N+1)).det*
      ((trueOddS N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det :=
  candidate_tail_det (trueOddS N) (odd_baseL_det_ne_zero hN) (odd_connection hN) s hs

end CP.Connection

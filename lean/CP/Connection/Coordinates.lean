import CP.Kernel.Odd.Nullspace
import CP.BlockElimination

namespace CP.Connection
open Matrix

/-- 行坐标：左部不动，右部反序。 -/
def pairedEquiv (m n : ℕ) : Fin (m+n) ≃ Fin (m+n) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin m)) Fin.revPerm).trans finSumFinEquiv)

/-- 列坐标：将原来的尾 m 个坐标移到前面，保持各自的内部次序。
这使已有 blocks 接口可用于纸面中行列分割大小相反的 B。 -/
def tailFirstEquiv (m n : ℕ) : Fin (m+n) ≃ Fin (m+n) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin m) (Fin n)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_comm n m))))

@[simp] theorem pairedEquiv_left (m n : ℕ) (i : Fin m) :
    pairedEquiv m n (Fin.castAdd n i) = Fin.castAdd n i := by simp [pairedEquiv]
@[simp] theorem pairedEquiv_right (m n : ℕ) (j : Fin n) :
    pairedEquiv m n (Fin.natAdd m j) = Fin.natAdd m j.rev := by simp [pairedEquiv]
@[simp] theorem tailFirstEquiv_left_val (m n : ℕ) (i : Fin m) :
    (tailFirstEquiv m n (Fin.castAdd n i)).val = n+i.val := by simp [tailFirstEquiv, Nat.add_comm]
@[simp] theorem tailFirstEquiv_right_val (m n : ℕ) (j : Fin n) :
    (tailFirstEquiv m n (Fin.natAdd m j)).val = j.val := by simp [tailFirstEquiv]

def LL {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  A.submatrix (Fin.castAdd n) (Fin.castAdd n)
def LR {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) : Matrix (Fin m) (Fin n) ℚ :=
  A.submatrix (Fin.castAdd n) (Fin.natAdd m)
def RL {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) : Matrix (Fin n) (Fin m) ℚ :=
  A.submatrix (Fin.natAdd m) (Fin.castAdd n)
def RR {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  A.submatrix (Fin.natAdd m) (Fin.natAdd m)

@[simp] theorem LL_blocks {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin m) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin m) ℚ) (D : Matrix (Fin n) (Fin n) ℚ) : LL (blocks A B C D) = A := by
  ext i j; simp [LL,blocks]
@[simp] theorem LR_blocks {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin m) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin m) ℚ) (D : Matrix (Fin n) (Fin n) ℚ) : LR (blocks A B C D) = B := by
  ext i j; simp [LR,blocks]
@[simp] theorem RL_blocks {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin m) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin m) ℚ) (D : Matrix (Fin n) (Fin n) ℚ) : RL (blocks A B C D) = C := by
  ext i j; simp [RL,blocks]
@[simp] theorem RR_blocks {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin m) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin m) ℚ) (D : Matrix (Fin n) (Fin n) ℚ) : RR (blocks A B C D) = D := by
  ext i j; simp [RR,blocks]

theorem blocks_reconstruct {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :
    blocks (LL A) (LR A) (RL A) (RR A) = A := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [LL,LR,RL,RR,blocks]

theorem blocks_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin m) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin m) ℚ) (D : Matrix (Fin n) (Fin n) ℚ) :
    (blocks A B C D)ᵀ = blocks Aᵀ Cᵀ Bᵀ Dᵀ := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [blocks,Matrix.transpose_apply]

def paired {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :=
  A.submatrix (pairedEquiv m n) (pairedEquiv m n)
def tailFirst {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :=
  A.submatrix (tailFirstEquiv m n) (tailFirstEquiv m n)

theorem paired_mul {m n : ℕ} (A B : Matrix (Fin (m+n)) (Fin (m+n)) ℚ) :
    paired (m:=m) (n:=n) (A*B) = paired A*paired B := by
  exact (Matrix.submatrix_mul_equiv A B (pairedEquiv m n) (pairedEquiv m n) (pairedEquiv m n)).symm

end CP.Connection

import CP.Connection.CandidateCongruence

namespace CP.Connection
open Matrix

noncomputable def evenEliminated (N : ℕ) := blocks (evenX N) (-evenX N) (evenX N) (H N N-evenX N)
noncomputable def evenEliminatedInverse (N : ℕ) :=
  blocks ((evenX N)⁻¹-(H N N)⁻¹) ((H N N)⁻¹) (-(H N N)⁻¹) ((H N N)⁻¹)

theorem evenEliminated_right_inverse {N : ℕ} (hN : 1 ≤ N) :
    evenEliminated N*evenEliminatedInverse N = 1 := by
  have hx : evenX N*(evenX N)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (evenX_det_ne_zero hN).isUnit
  have hh : H N N*(H N N)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_H]; exact isUnit_one)
  have he := elimination_right_inverse (evenX N) (evenX N)⁻¹ (H N N) (H N N)⁻¹ 1 (evenX N) hx hh
  simpa only [evenEliminated,evenEliminatedInverse,Matrix.mul_one,Matrix.one_mul,
    Matrix.mul_assoc,hx] using he

theorem evenEliminated_inverse {N : ℕ} (hN : 1 ≤ N) :
    (evenEliminated N)⁻¹ = evenEliminatedInverse N := by
  exact even_elimination_inverse _ _ _ _
    (Matrix.mul_nonsing_inv _ (evenX_det_ne_zero hN).isUnit)
    (Matrix.mul_nonsing_inv _ (by rw [det_H]; exact isUnit_one))

theorem connectionB_det_ne_zero (m n : ℕ) : (connectionB m n).det ≠ 0 := by
  have he := congrArg Matrix.det (paired_G_gram m n)
  rw [Matrix.det_mul,Matrix.det_transpose] at he
  have hg : (paired (m:=m) (n:=n) (G (m+n))).det = 1 := by
    rw [paired,Matrix.det_submatrix_equiv_self,det_G]
  rw [hg] at he
  intro hz
  rw [hz,zero_mul] at he
  exact one_ne_zero he

theorem even_baseL_det_ne_zero {N : ℕ} (hN : 1 ≤ N) : (baseL N N).det ≠ 0 := by
  have hs : (evenEliminated N).det ≠ 0 :=
    det_ne_zero_from_right_inverse _ _ (evenEliminated_right_inverse hN)
  have he := congrArg Matrix.det (even_baseL_congruence N)
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose] at he
  have hl : (tailFirst (m:=N) (n:=N) (baseL N N)).det = (baseL N N).det := by
    rw [tailFirst,Matrix.det_submatrix_equiv_self]
  rw [hl] at he
  intro hz
  rw [hz,mul_zero,zero_mul] at he
  exact hs he.symm

/-- 合同逆完整地回到候选坐标；此处尚未取任何主块。 -/
theorem even_candidate_inverse {N : ℕ} (hN : 1 ≤ N) :
    (tailFirst (m:=N) (n:=N) (baseL N N))⁻¹ =
      (connectionB N N)ᵀ*evenEliminatedInverse N*connectionB N N := by
  have hB : (connectionB N N)⁻¹*connectionB N N = 1 :=
    Matrix.nonsing_inv_mul _ (connectionB_det_ne_zero N N).isUnit
  have hc := even_baseL_congruence N
  change connectionB N N*tailFirst (m:=N) (n:=N) (baseL N N)*(connectionB N N)ᵀ = evenEliminated N at hc
  apply Matrix.inv_eq_right_inv
  calc
    _ = ((connectionB N N)⁻¹*connectionB N N)*tailFirst (m:=N) (n:=N) (baseL N N)*
        (connectionB N N)ᵀ*evenEliminatedInverse N*connectionB N N := by
      rw [hB,Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    _ = (connectionB N N)⁻¹*(connectionB N N*tailFirst (m:=N) (n:=N) (baseL N N)*
        (connectionB N N)ᵀ)*evenEliminatedInverse N*connectionB N N := by
      simp only [Matrix.mul_assoc]
    _ = (connectionB N N)⁻¹*(evenEliminated N*evenEliminatedInverse N)*connectionB N N := by
      rw [hc]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [evenEliminated_right_inverse hN,Matrix.mul_one,hB]

/-- 候选逆的原尾块在尾部优先置换后的 LL 块公式。 -/
theorem even_candidate_tail_formula {N : ℕ} (hN : 1 ≤ N) :
    LL (tailFirst (m:=N) (n:=N) ((baseL N N)⁻¹)) =
      (B N)ᵀ*(evenX N)⁻¹*B N-(B N)ᵀ*(H N N)⁻¹*B N+
      (B N)ᵀ*(H N N)⁻¹*Y N N-(Y N N)ᵀ*(H N N)⁻¹*B N+
      (Y N N)ᵀ*(H N N)⁻¹*Y N N := by
  have hi : tailFirst (m:=N) (n:=N) ((baseL N N)⁻¹) =
      (tailFirst (m:=N) (n:=N) (baseL N N))⁻¹ := by
    exact (Matrix.inv_submatrix_equiv _ (tailFirstEquiv N N) (tailFirstEquiv N N)).symm
  rw [hi,even_candidate_inverse hN,connectionB_blocks,blocks_transpose,
    evenEliminatedInverse,blocks_mul,blocks_mul,LL_blocks]
  noncomm_ring

end CP.Connection

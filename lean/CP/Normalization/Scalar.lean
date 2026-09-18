import CP.Normalization.OddBorder

namespace CP.Connection
open Matrix CP.Kernel Finset

@[simp] theorem tailDiagonal_zero (q : ℕ) : tailDiagonal q 0 = 0 := by
  ext i j
  simp [tailDiagonal,Matrix.diagonal_apply,not_le.mpr i.isLt]

@[simp] theorem kernelTail_zero (m : ℕ) (D : Matrix (Fin m) (Fin m) ℚ) :
    D.submatrix (kernelTail m 0 (Nat.zero_le m)) (kernelTail m 0 (Nat.zero_le m)) = D := by
  ext i j
  have he (i : Fin m) : kernelTail m 0 (Nat.zero_le m) i = i := by apply Fin.ext; simp [kernelTail]
  simp only [Matrix.submatrix_apply,he]

@[simp] theorem borderTail_zero (N : ℕ) (D : Matrix (Fin (N+1)) (Fin (N+1)) ℚ) :
    D.submatrix (borderTail N 0 (Nat.zero_le N)) (borderTail N 0 (Nat.zero_le N)) = D := by
  ext i j
  have he (i : Fin (N+1)) : borderTail N 0 (Nat.zero_le N) i = i := by apply Fin.ext; simp [borderTail]
  simp only [Matrix.submatrix_apply,he]

/-- N1 的偶数标量行列式关系，完全属于有限代数。 -/
theorem even_scalar_relation (N : ℕ) (hN : 1 ≤ N) :
    (K (N+N)).det = (baseL N N).det*(trueD N).det := by
  simpa only [tailDiagonal_zero,sub_zero,kernelTail_zero] using even_finite_bridge N hN 0 (Nat.zero_le N)

/-- N1 的奇数标量行列式关系，完全属于有限代数。 -/
theorem odd_scalar_relation (N : ℕ) (hN : 1 ≤ N) :
    (K (N+(N+1))).det = (baseL N (N+1)).det*(trueOddS N).det := by
  simpa only [tailDiagonal_zero,sub_zero,kernelTail_zero] using odd_finite_bridge N hN 0 (Nat.zero_le N)

theorem trueE_det (N : ℕ) : (trueE N).det = nu N (oddCenter N)*(trueOddS N).det := by
  simpa only [kernelTail_zero,borderTail_zero] using trueE_tail_det N 0 (Nat.zero_le N)

/-- 无绝对枚举输入的实际偶数行列式比关系，亦允许端点空尾块。 -/
theorem even_relative_bridge (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s ≤ N) :
    (K (N+N)-tailDiagonal (N+N) s).det*(trueD N).det =
      (K (N+N)).det*((trueD N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det := by
  rw [even_finite_bridge N hN s hs,even_scalar_relation N hN]
  ring

/-- 无绝对枚举输入的实际奇数有边框核行列式比关系。 -/
theorem odd_relative_bridge (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s ≤ N) :
    (K (N+(N+1))-tailDiagonal (N+(N+1)) s).det*(trueE N).det =
      (K (N+(N+1))).det*((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det := by
  rw [odd_finite_bridge N hN s hs,odd_scalar_relation N hN,trueE_det,trueE_tail_det]
  ring

/-- 奇数有边框核的无条件绝对有限关系：唯一代数标量为 det L / α。 -/
theorem odd_bordered_finite_bridge (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s ≤ N) :
    (K (N+(N+1))-tailDiagonal (N+(N+1)) s).det =
      ((baseL N (N+1)).det/nu N (oddCenter N))*
        ((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det := by
  rw [odd_finite_bridge N hN s hs,trueE_tail_det]
  have hc : nu N (oddCenter N) ≠ 0 := (nu_center_pos N).ne'
  field_simp [hc]
  ring

/-- 外部枚举归一化中使用的精确有理数乘积；此定义不声称它已被证明枚举 ASM。 -/
def asmProduct (n : ℕ) : ℚ :=
  ∏ i : Fin n, (Nat.factorial (3*i.val+1) : ℚ)/(Nat.factorial (n+i.val) : ℚ)

theorem asmProduct_pos (n : ℕ) : 0 < asmProduct n := by
  apply Finset.prod_pos
  intro i hi
  apply div_pos <;> exact_mod_cast Nat.factorial_pos _

/-- 两个明确的阶段外输入：候选 det K 的已知总枚举值，以及真实端 s=0 的公式。
该结构没有默认实例；本工程不构造其中的证明。 -/
structure EvenNormalizationInput (N : ℕ) : Prop where
  candidate_total : (K (N+N)).det = asmProduct (N+N)
  unfrozen_true : asmProduct (N+N) = asmProduct N^2*(trueD N).det

/-- 奇数归一化输入使用真实有边框核，未以非平凡冻结值归一化。 -/
structure OddNormalizationInput (N : ℕ) : Prop where
  candidate_total : (K (N+(N+1))).det = asmProduct (N+(N+1))
  unfrozen_true : asmProduct (N+(N+1)) = asmProduct N^2*(trueE N).det

/-- (9.2) 偶数绝对标量：条件只在清晰的阶段外接口中。 -/
theorem even_scalar_normalized (N : ℕ) (hN : 1 ≤ N) (h : EvenNormalizationInput N) :
    (baseL N N).det = asmProduct N^2 := by
  have hd : (trueD N).det ≠ 0 := by
    intro hz
    have he := h.unfrozen_true
    rw [hz,mul_zero] at he
    exact (asmProduct_pos (N+N)).ne' he
  apply mul_right_cancel₀ hd
  rw [← even_scalar_relation N hN,h.candidate_total,h.unfrozen_true]

/-- (9.2) 奇数绝对标量，中心 α 保持为实际 ν_N。 -/
theorem odd_scalar_normalized (N : ℕ) (hN : 1 ≤ N) (h : OddNormalizationInput N) :
    (baseL N (N+1)).det = asmProduct N^2*nu N (oddCenter N) := by
  have hd : (trueOddS N).det ≠ 0 := by
    intro hz
    have he := h.unfrozen_true
    rw [trueE_det,hz,mul_zero,mul_zero] at he
    exact (asmProduct_pos (N+(N+1))).ne' he
  apply mul_right_cancel₀ hd
  rw [← odd_scalar_relation N hN,h.candidate_total,h.unfrozen_true,trueE_det]
  ring

/-- 全部允许 s 的绝对偶数有限桥；ASM 解释只存在于显式外部输入。 -/
theorem even_bridge_normalized (N : ℕ) (hN : 1 ≤ N) (h : EvenNormalizationInput N)
    (s : ℕ) (hs : s ≤ N) :
    (K (N+N)-tailDiagonal (N+N) s).det = asmProduct N^2*
      ((trueD N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det := by
  rw [even_finite_bridge N hN s hs,even_scalar_normalized N hN h]

/-- 全部允许 s 的绝对奇数有限桥，右端是实际 ℰ 尾块。 -/
theorem odd_bridge_normalized (N : ℕ) (hN : 1 ≤ N) (h : OddNormalizationInput N)
    (s : ℕ) (hs : s ≤ N) :
    (K (N+(N+1))-tailDiagonal (N+(N+1)) s).det = asmProduct N^2*
      ((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det := by
  rw [odd_finite_bridge N hN s hs,odd_scalar_normalized N hN h,trueE_tail_det]
  ring

end CP.Connection

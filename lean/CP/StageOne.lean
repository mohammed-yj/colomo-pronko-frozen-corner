import CP.Normalization.Scalar

/-! 第一阶段验收接口。以下仅涉及有限代数。
绝对乘积归一化由显式的阶段外输入参数承担；本文件不宣称 ASM 端到端定理。 -/
namespace CP.StageOne
open Matrix CP.Connection

/-- 无条件偶数有限桥，规范的 2N 尺寸。 -/
theorem even_finite_bridge (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s ≤ N) :
    (K (2*N)-tailDiagonal (2*N) s).det =
      (K (2*N)-tailDiagonal (2*N) N).det*
        ((trueD N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det := by
  let P (q : ℕ) := (K q-tailDiagonal q s).det =
    (K q-tailDiagonal q N).det*((trueD N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det
  have hp : P (N+N) := CP.Connection.even_finite_bridge N hN s hs
  exact (congrArg P (show N+N=2*N by omega)).mp hp

/-- 无条件奇数有限桥，右端为实际有边框核，α 已证明非零。 -/
theorem odd_finite_bridge (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s ≤ N) :
    (K (2*N+1)-tailDiagonal (2*N+1) s).det =
      ((K (2*N+1)-tailDiagonal (2*N+1) N).det/CP.Kernel.nu N (oddCenter N))*
        ((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det := by
  let P (q : ℕ) := (K q-tailDiagonal q s).det =
    ((K q-tailDiagonal q N).det/CP.Kernel.nu N (oddCenter N))*
      ((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det
  have hp : P (N+(N+1)) := odd_bordered_finite_bridge N hN s hs
  exact (congrArg P (show N+(N+1)=2*N+1 by omega)).mp hp

/-- 仅以明确 s=0 外部接口接入 A_N² 的偶数结论。 -/
theorem even_normalized (N : ℕ) (hN : 1 ≤ N) (h : EvenNormalizationInput N)
    (s : ℕ) (hs : s ≤ N) :
    (K (2*N)-tailDiagonal (2*N) s).det = asmProduct N^2*
      ((trueD N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det := by
  let P (q : ℕ) := (K q-tailDiagonal q s).det = asmProduct N^2*
    ((trueD N).submatrix (kernelTail N s hs) (kernelTail N s hs)).det
  have hp : P (N+N) := even_bridge_normalized N hN h s hs
  exact (congrArg P (show N+N=2*N by omega)).mp hp

/-- 仅以明确 s=0 外部接口接入 A_N² 的奇数结论。 -/
theorem odd_normalized (N : ℕ) (hN : 1 ≤ N) (h : OddNormalizationInput N)
    (s : ℕ) (hs : s ≤ N) :
    (K (2*N+1)-tailDiagonal (2*N+1) s).det = asmProduct N^2*
      ((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det := by
  let P (q : ℕ) := (K q-tailDiagonal q s).det = asmProduct N^2*
    ((trueE N).submatrix (borderTail N s hs) (borderTail N s hs)).det
  have hp : P (N+(N+1)) := odd_bridge_normalized N hN h s hs
  exact (congrArg P (show N+(N+1)=2*N+1 by omega)).mp hp

end CP.StageOne

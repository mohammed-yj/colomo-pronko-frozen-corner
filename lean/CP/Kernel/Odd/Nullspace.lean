import CP.Kernel.Odd.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace CP.Kernel
open Matrix Finset

theorem nu_ne_zero (N : ℕ) : nu N ≠ 0 := by
  intro he
  have hp := nu_center_pos N
  rw [he, Pi.zero_apply] at hp
  exact (lt_irrefl 0) hp

/-- 整个奇数零空间中的每个向量都是规范 ν 的标量倍。 -/
theorem omega_kernel_vector {N : ℕ} (hN : 1 ≤ N) (v : Fin (2*N+1) → ℚ)
    (hv : omega (2*N+1) *ᵥ v = 0) :
    v = ((fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N)) ⬝ᵥ v) • nu N := by
  have hh : (1-Matrix.vecMulVec (nu N)
      (fun i => alternating (2*N+1) i/(alternating (2*N+1) ⬝ᵥ nu N))) *ᵥ v = 0 := by
    rw [← gammaOdd_omega hN, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hh
  funext i
  have he := congrFun hh i
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply] at he
  simp only [mul_assoc, ← Finset.mul_sum] at he
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct]
  linear_combination he

/-- 明确的一维零空间等式，未将有限参数验证用作秩证明。 -/
theorem omega_kernel_eq_span {N : ℕ} (hN : 1 ≤ N) :
    LinearMap.ker (omega (2*N+1)).mulVecLin = Submodule.span ℚ {nu N} := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
  constructor
  · intro hv
    exact ⟨_, (omega_kernel_vector hN v hv).symm⟩
  · rintro ⟨r, rfl⟩
    rw [Matrix.mulVec_smul, omega_nu_zero, smul_zero]

theorem omega_kernel_finrank {N : ℕ} (hN : 1 ≤ N) :
    Module.finrank ℚ (LinearMap.ker (omega (2*N+1)).mulVecLin) = 1 := by
  rw [omega_kernel_eq_span hN]
  exact finrank_span_singleton (nu_ne_zero N)

/-- O2：奇数交换子的秩恰为 2N。 -/
theorem omega_odd_rank {N : ℕ} (hN : 1 ≤ N) : (omega (2*N+1)).rank = 2*N := by
  have he := LinearMap.finrank_range_add_finrank_ker (omega (2*N+1)).mulVecLin
  rw [omega_kernel_finrank hN, Module.finrank_pi] at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at he
  change (omega (2*N+1)).rank+1 = 2*N+1 at he
  omega

end CP.Kernel

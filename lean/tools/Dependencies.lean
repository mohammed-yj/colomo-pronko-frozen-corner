import CP
import Lean.Util.FoldConsts

/- 此文件只生成环境依赖报告，不被任何数学证明模块导入。 -/
open Lean Elab Command

elab "#cp_project_dependencies " decl:ident : command => do
  let root := decl.getId
  let env ← getEnv
  unless env.contains root do throwError "unknown declaration: {root}"
  let mut todo : List Name := [root]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    unless seen.contains name do
      seen := seen.insert name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet do
          if dep.toString.startsWith "CP." then
            todo := dep :: todo
  let names := seen.toArray.qsort (fun a b => a.toString < b.toString)
  logInfo m!"CP_DEPENDENCIES {root}\n{String.intercalate "\n" (names.toList.map Name.toString)}"

#cp_project_dependencies CP.Fractional.fractional_substitution
#cp_project_dependencies CP.Fractional.fractional_cleared
#cp_project_dependencies CP.Fractional.fractional_truncation
#cp_project_dependencies CP.Recurrence.three_term_recurrence
#cp_project_dependencies CP.Adjacent.adjacent_pair

#cp_project_dependencies CP.Kernel.sigma_u
#cp_project_dependencies CP.Kernel.sigma_v
#cp_project_dependencies CP.Kernel.sigma_uStar
#cp_project_dependencies CP.Kernel.sigma_vStar
#cp_project_dependencies CP.Kernel.uvStar_pair
#cp_project_dependencies CP.Kernel.denominator_dvd_pNumerator
#cp_project_dependencies CP.Kernel.pKernel_degree
#cp_project_dependencies CP.Kernel.swap_pKernel_degree
#cp_project_dependencies CP.Kernel.pKernel_reflection
#cp_project_dependencies CP.Kernel.pMatrix_reflection

#cp_project_dependencies CP.Series.G_mulVec_coeff
#cp_project_dependencies CP.Series.G_R_inverse_apply
#cp_project_dependencies CP.Series.rationalKernel_denominator
#cp_project_dependencies CP.Series.even_G_R_inverse_kernel

#cp_project_dependencies CP.Kernel.cMatrix_reflection
#cp_project_dependencies CP.Kernel.cKernel_sigma_cleared
#cp_project_dependencies CP.Kernel.cKernel_series_exact
#cp_project_dependencies CP.Kernel.G_cMatrix
#cp_project_dependencies CP.Kernel.omega_mul_J_sub_C
#cp_project_dependencies CP.Kernel.omega_inverse_eq_J_sub_C
#cp_project_dependencies CP.Kernel.omega_det_ne_zero

#cp_project_dependencies CP.Kernel.G_inverse_lift_update
#cp_project_dependencies CP.Kernel.oMatrix_lift
#cp_project_dependencies CP.Kernel.gammaOdd_eq_lift_inverse
#cp_project_dependencies CP.Kernel.omega_nu_zero
#cp_project_dependencies CP.Kernel.omega_kernel_eq_span
#cp_project_dependencies CP.Kernel.omega_odd_rank
#cp_project_dependencies CP.Kernel.omega_gammaOdd
#cp_project_dependencies CP.Kernel.odd_deleted_inverse
#cp_project_dependencies CP.Kernel.odd_deleted_mul_inverse

#cp_project_dependencies CP.Connection.trueD_eq_freeD_add_inverse
#cp_project_dependencies CP.Connection.even_baseL_congruence
#cp_project_dependencies CP.Connection.even_candidate_inverse
#cp_project_dependencies CP.Connection.freeD_congruence
#cp_project_dependencies CP.Connection.even_connection_native
#cp_project_dependencies CP.Connection.trueD_apply
#cp_project_dependencies CP.Connection.trueOddS_projected_fold

#cp_project_dependencies CP.Connection.odd_fold_right_inverse
#cp_project_dependencies CP.Connection.odd_fold_inverse
#cp_project_dependencies CP.Connection.trueOddS_eq_free_add_inverse
#cp_project_dependencies CP.Connection.odd_baseL_congruence
#cp_project_dependencies CP.Connection.oddEliminated_inverse
#cp_project_dependencies CP.Connection.oddZ_center_row
#cp_project_dependencies CP.Connection.oddZ_mul_inverse
#cp_project_dependencies CP.Connection.freeOddS_inverseGram
#cp_project_dependencies CP.Connection.freeOddS_congruence
#cp_project_dependencies CP.Connection.odd_candidate_inverse
#cp_project_dependencies CP.Connection.odd_connection_native
#cp_project_dependencies CP.Connection.candidate_add_back
#cp_project_dependencies CP.Connection.reversed_front_det
#cp_project_dependencies CP.Connection.even_finite_bridge
#cp_project_dependencies CP.Connection.odd_finite_bridge
#cp_project_dependencies CP.Connection.trueE_tail_det
#cp_project_dependencies CP.Connection.even_scalar_relation
#cp_project_dependencies CP.Connection.odd_scalar_relation
#cp_project_dependencies CP.Connection.even_relative_bridge
#cp_project_dependencies CP.Connection.odd_relative_bridge
#cp_project_dependencies CP.Connection.odd_bordered_finite_bridge
#cp_project_dependencies CP.Connection.even_scalar_normalized
#cp_project_dependencies CP.Connection.odd_scalar_normalized
#cp_project_dependencies CP.StageOne.even_finite_bridge
#cp_project_dependencies CP.StageOne.odd_finite_bridge
#cp_project_dependencies CP.StageOne.even_normalized
#cp_project_dependencies CP.StageOne.odd_normalized

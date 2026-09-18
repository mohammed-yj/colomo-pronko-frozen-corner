# Formalization scope

This statement is based on the final submission's source declarations and a fresh build, not on historical status reports. All theorem names below refer to the preserved sources under `lean/`. The exact correspondence is in [PAPER_MAP.md](PAPER_MAP.md). Build and axiom evidence is in [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Kernel-checked mathematics

The objects are explicit rational polynomials and matrices indexed by `Fin`; they are not defined by assuming the identities to be proved.

| Paper component | Formal declarations and qualification |
| --- | --- |
| Lemmas 3.1–3.3, explicit refined-polynomial algebra | `CP.Fractional.fractional_substitution`, `fractional_cleared`, `fractional_truncation`; `CP.Recurrence.three_term_recurrence`; `CP.Adjacent.adjacent_pair`. These concern the explicit polynomial, not its combinatorial interpretation. |
| Appendix A / supplement S.1 | `CP.recurrence_certificate`: one identity for arbitrary rational `a,m`, proved by `ring`; not a finite sample. Recurrence modules separately discharge coefficient ranges and denominators. |
| Lemma 5.1 and Lemma 7.1, polynomial kernels | `CP.Kernel.denominator_dvd_cNumerator`, `cKernel_degree`, `swap_cKernel_degree`, `cMatrix_skew`, `cMatrix_reflection`; corresponding `pKernel` divisibility/degree/reflection declarations. |
| Finite binomial operators and exact truncation, §7 | `CP.T_sq`, `B_mul_T`, `B_gram`, `K_congruence`; `CP.Series.G_mulVec_coeff`, `G_R_inverse_apply`; `CP.Kernel.cKernel_series_exact`, `G_cMatrix`. |
| Theorem 7.2, even inverse, all `N ≥ 1` | `CP.Kernel.omega_mul_J_sub_C`, `omega_inverse_eq_J_sub_C`, `omega_det_ne_zero`. No enumeration-normalization input. |
| §8, odd lift, nullspace, rank | `CP.Kernel.G_inverse_lift_update`, `oMatrix_lift`, `gammaOdd_eq_lift_inverse`, `omega_nu_zero`, `omega_kernel_eq_span`, `omega_kernel_finrank`, `omega_odd_rank`. The odd commutator has rank `2*N` and kernel spanned by the explicit nonzero vector `nu`. |
| §8, central projection and deleted inverse | `CP.Kernel.omega_gammaOdd`, `odd_deleted_inverse`, `odd_deleted_mul_inverse`; `CP.centered_deleted_inverse`. Projection precedes deletion. |
| §9, block elimination and both connections | `CP.elimination_inverse`, `even_elimination_inverse`; `CP.Connection.even_candidate_inverse`, `oddEliminated_inverse`, `odd_candidate_inverse`; `even_connection_native`, `odd_connection_native`. The word `native` means original matrix coordinates, not `native_decide`. |
| §10, diagonal add-back, leading congruence | `CP.det_diagonal_add_back`, `det_front_congruence`; `CP.Connection.candidate_add_back`, `reversed_front_det`, `trueE_tail_det`. |
| (10.5), relative finite bridges, arbitrary allowed parameters | `CP.StageOne.even_finite_bridge`, `CP.StageOne.odd_finite_bridge`, with `N ≥ 1`, `s ≤ N`; no normalization records. |
| Algebraic part of (10.6)–(10.7) with `A_N²` | `CP.StageOne.even_normalized`, `CP.StageOne.odd_normalized`, conditional on the following explicit records. They do not state equality with an ASM counting function. |

## Exact external normalization hypotheses

`CP.Connection.asmProduct n` is an explicit rational factorial product. Lean proves its positivity, but does not prove that it counts ASMs. In `CP/Normalization/Scalar.lean`:

```text
EvenNormalizationInput N:
  candidate_total: det K_(2N) = asmProduct (2N)
  unfrozen_true:   asmProduct (2N) = asmProduct N ^ 2 * det(trueD N)

OddNormalizationInput N:
  candidate_total: det K_(2N+1) = asmProduct (2N+1)
  unfrozen_true:   asmProduct (2N+1) = asmProduct N ^ 2 * det(trueE N)
```

These are `Prop` structures passed as arguments; no project axiom or default instance supplies them. Their paper justification is Proposition 4.1 at zero deformation and Theorem 6.1 at `s=0`, using the ASM enumeration input. Even and odd normalized statements conclude equality between `det(K − E)` and `asmProduct N ^ 2` times the appropriate tail determinant. The relative statements and even core inverse are audited to have no dependency on either record.

## Paper proof and external inputs

Theorem 2.1 is a paper theorem, not an end-to-end Lean theorem. No Lean definition in this project counts ASMs. Theorem 6.1 as an enumeration theorem, Proposition 4.1 as the identity between the CP residue matrix and the binomial candidate, the CP24 integral, analytic contour/residue arguments, Pfaffian evaluation/folding as an enumeration derivation, combinatorial endpoint/forbidden-range arguments, and Corollary 2.2 are outside end-to-end formalization. Finite matrix algebra supporting these steps is mapped separately; its existence does not formalize their enumerative interpretation.

[EXTERNAL_INTERFACES.md](EXTERNAL_INTERFACES.md) distinguishes literature assumptions, results reproved on paper, background references, and inputs crossing the Lean boundary. The paper's final closure uses both candidate identification and true enumeration determinants, then the normalized finite bridges and endpoints. None of these interfaces is silently asserted as a Lean axiom.

## Computation and trust

Proof modules contain no `sorry`, `admit`, custom axiom declarations, `native_decide`, or unsafe proof definitions. Theorems are kernel checked. Tactics including `ring`, `norm_num`, `omega`, `simp`, and finite-sum algebra construct proof terms; their use is not an external Boolean certificate. No project proof uses `decide` or Boolean reflection as a replacement for proof checking. The systematic audit permits only the standard dependencies `propext`, `Classical.choice`, and `Quot.sound` and fails on any other axiom.

The preserved `tools/frontend.lean` contains an `unsafe` IO/frontend driver with explicit `trustLevel := 0`. It is build tooling, is not imported by the proof modules, and introduces no mathematical axiom. The documented standard `lake build CP CP.Axioms` and CI use the official Lean compiler directly. The additional `AllAxioms.lean` audits all project theorem declarations in the loaded environment, including compiler-generated theorem declarations. The original `CP/Axioms.lean` remains available as a separate explicit `#print axioms` audit.

Python/SymPy checks execute outside the Lean kernel. Only the recurrence polynomial certificate is an exact universal polynomial identity; the finite matrix/counting ranges do not establish parameterized theorems.

## Differences from older descriptions

The final code covers more than a standalone inverse certificate: it includes actual refined-polynomial identities, kernel divisibility/truncation, both connections, and arbitrary-`s` finite bridges. Conversely, the full enumeration theorem and absolute normalization are not unconditional Lean conclusions. Some unchanged source comments retain earlier stage terminology, equation numbers, or “not yet instantiated” wording (notably `CP/FiniteBridge.lean`); later `Connection`, `Normalization`, and `StageOne` declarations supply those instantiations. Actual theorem types and dependencies govern this scope statement.

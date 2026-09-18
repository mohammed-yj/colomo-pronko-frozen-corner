# Reproducibility

## Fixed versions

- Python **3.12.14**; SymPy **1.14.0**; mpmath **1.3.0** (the exact checks use rational/integer arithmetic, not floating-point inference).
- Lean **4.19.0**, toolchain `leanprover/lean4:v4.19.0`; local compiler commit `6caaee842e94`.
- mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**.
- `lean/lake-manifest.json` pins all nine package revisions; `lean/lakefile.lean` also pins mathlib directly. The lockfile is preserved from the final submission.
- GitHub Actions pins checkout/setup-python/upload-artifact to commit SHAs and uses Ubuntu 24.04. The elan bootstrap script is pinned; the mathematical compiler version is separately fixed by `lean-toolchain`.

## Exact and symbolic checks

From the repository root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r verification/requirements.txt
python scripts/audit_sources.py
python verification/symbolic_certificate.py
python verification/exact_checks.py
```

The symbolic check rebuilds Appendix A's eight terms from the seven rational coefficient ratios, compares each to supplement S.1, proves the sum is the zero polynomial over the integers, and compares the preserved Lean certificate expression. The denominator's nonvanishing on the allowed range is supplied by the paper and the Lean recurrence proof, not inferred from numerical tests.

The separate exact regression program builds all input polynomials and matrices from their definitions:

| Check | Fixed rerun range | Method |
| --- | --- | --- |
| Refined-polynomial normalization, palindrome, fractional substitution, recurrence and adjacent identity | `m=1..20`, where each identity is applicable | Exact univariate rational/polynomial algebra |
| CP residue candidate versus `det(K−lambda E)` | `n=1..8`, every `s=0..n` | Residue coefficients computed directly from the CP definition; `s+1` exact lambda evaluations identify the degree-at-most-`s` polynomial |
| Independent frozen-corner enumeration | `n=1..8`, every `s=0..n` | Dynamic counting of strictly increasing interlacing monotone-triangle rows; row `s` lies in `s+1..n`; does not use the determinant to generate counts |
| Binomial operators, Gram/congruence identities, `det K=A`, forbidden range | `n=1..12`, all applicable `s` | Exact integer/rational matrices and determinants |
| Actual even/odd kernels, divisibility, inverses, lift, nullspace/rank, central projection, native-coordinate connections | `N=1..6` | Independently construct the rational kernel, divide polynomials exactly, and check the resulting matrices |
| Relative and absolute bridges, including empty tails and the odd central border | `N=1..6`, every `s=0..N` | Determinants reconstructed from explicit coefficients; normalization checked against the factorial product |
| Even/odd Pfaffian folding | `N=1..6`, every `s=0..N` | Recursive exact Pfaffian expansion compared with the respective folded determinant |

These finite ranges are consistency checks. They do not prove the full conjecture, certify historical experiments, or inhabit the Lean normalization records. No historical proof-search program or pre-generated experimental output is used as an oracle. The only standalone universal polynomial certificate is `certificates/recurrence.json`, also proved parametrically in Lean.

## Fresh Lean build and audits

From a new checkout with the fixed Lean toolchain installed:

```sh
python3 scripts/audit_sources.py
cd lean
lake exe cache get
python3 ../scripts/check_dependency_revisions.py
lean --version
lake build CP CP.Axioms
lake env lean tools/AllAxioms.lean > ../.audit/all-axioms.txt
lake env lean tools/Dependencies.lean > ../.audit/dependencies.txt
cd ..
python3 scripts/check_lean_audit.py .audit/all-axioms.txt .audit/dependencies.txt
python3 scripts/audit_sources.py
```

`lake exe cache get` downloads compiled **dependencies**, not project proofs. The fresh local build started with no compiled project artifacts, using revision-verified existing dependency caches. All project modules were compiled from the exact public source. The build completed successfully. The full local record is [certificates/fresh-lean-build.json](certificates/fresh-lean-build.json): **51 nonfatal linter warnings**, all recorded with source locations and messages, concerning unnecessary `simpa`/sequence focus or ineffective/unexecuted tactics. Proof sources were not altered to remove cosmetic warnings.

`CP/Axioms.lean` contains 550 explicit `#print axioms` commands (including repeated/overlapping coverage). The stronger environment-wide audit checks **1,103 project theorem declarations**, including automatically generated auxiliary theorems, and rejects every dependency except `propext`, `Classical.choice`, and `Quot.sound`. It also compares with the committed per-theorem inventory. `tools/Dependencies.lean` inspects **69 roots**; the checker verifies coverage, confirms eight core roots are independent of normalization records, and confirms both normalized StageOne results retain the records. See [FORMALIZATION_SCOPE.md](FORMALIZATION_SCOPE.md).

The preserved default Lake target `checked` additionally offers the original official-frontend driver with `trustLevel := 0`. It is not needed for the commands above. To use that optional target, set `LEAN_SYSROOT` to the installed toolchain root and run `lake build checked`. The published fresh-build result and CI are explicitly for the standard targets `CP CP.Axioms`, not a claim to have rerun that optional driver.

## CI and evidence

`.github/workflows/verify.yml` runs two independent jobs: exact symbolic/determinant checks, and fresh Lean build/axiom/dependency audit. Both validate the file allowlist and hashes; neither accesses the original research directory. CI starts with a clean checkout, fetches pinned dependencies, compiles project modules, and rebuilds the audit reports. Fresh CI build/axiom/dependency evidence is uploaded as the `lean-audit` workflow artifact. Runtime `.audit/`, `.lake/`, and `.venv/` are excluded from Git.

The repository does not rebuild or edit the already-approved paper PDFs. Its four paper files are hashed, byte-preserved publication artifacts; reproducing the mathematics and formal checks does not require LaTeX or historical local paths.

# Colomo–Pronko frozen-corner alternating sign matrices

Reproducibility companion to **Yinjie Li, _The Colomo–Pronko conjecture for frozen-corner alternating sign matrices_**. The authoritative paper and supplement are preserved in [paper/](paper/).

Let `B(n,s)` count `n × n` alternating sign matrices whose top-left `s × s` square is zero, and let `A(n)` be the total ASM count. The Colomo–Pronko conjecture identifies `B(n,s)/A(n)` with their explicit frozen-corner determinant `det(I_s − M)`. The paper proves this identity for every `n ≥ 1` and `0 ≤ s ≤ n`, including the zero range `2s > n`. Together with Colomo and Pronko's external determinant asymptotics, the paper derives a one-point GUE Tracy–Widom limit for the diagonal boundary coordinate.

**Lean checks the finite-dimensional algebraic core over the rationals.** It proves refined-polynomial identities, polynomial kernel divisibility and exact truncation, the even inverse, odd lifting/nullspace/central projection, both matrix connections, and finite bridges for every admissible `N,s`. The normalized bridges require explicit `EvenNormalizationInput` or `OddNormalizationInput` hypotheses. ASM enumeration, the multiple-integral input, its analytic/Pfaffian evaluation, the identification of the original CP/FR candidate, and the probabilistic corollary remain paper proofs or external inputs. See [FORMALIZATION_SCOPE.md](FORMALIZATION_SCOPE.md), [EXTERNAL_INTERFACES.md](EXTERNAL_INTERFACES.md), and [PAPER_MAP.md](PAPER_MAP.md).

The repository contains:

- The final paper/supplement PDF and TeX, unchanged.
- The final submission's Lean proof sources, pinned to Lean **4.19.0** and mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**.
- The eight-term integer-polynomial recurrence certificate, with independent symbolic reconstruction.
- Exact rational matrix checks and independent monotone-triangle counting, rebuilt for this release. Finite checks are consistency evidence, not proofs for arbitrary parameters.
- Build, theorem-axiom, dependency, preservation, and publication audits.

## Reproduce

With Python 3.12.14 and the pinned Lean toolchain installed:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r verification/requirements.txt
python verification/symbolic_certificate.py
python verification/exact_checks.py
python scripts/audit_sources.py
cd lean
lake exe cache get
lake build CP CP.Axioms
lake env lean tools/AllAxioms.lean > ../.audit/all-axioms.txt
lake env lean tools/Dependencies.lean > ../.audit/dependencies.txt
cd ..
python scripts/check_lean_audit.py .audit/all-axioms.txt .audit/dependencies.txt
```

`audit_sources.py` creates `.audit/`. Full commands, exact ranges, fresh-build evidence, warnings, and the trust boundary are in [REPRODUCIBILITY.md](REPRODUCIBILITY.md). [GitHub Actions](https://github.com/mohammed-yj/colomo-pronko-frozen-corner/actions) independently rebuilds the checks.

## Paper and citation

Use [CITATION.cff](CITATION.cff). The supplied final paper has no verified arXiv identifier or DOI of its own; none is assigned here. The Colomo–Pronko and Fischer–Reibnegger identifiers in its bibliography belong to those authors' papers. Release information, if subsequently created, appears on the [repository Releases page](https://github.com/mohammed-yj/colomo-pronko-frozen-corner/releases).

## License and provenance

MIT applies to original Lean/code, certificates, and repository documentation. **The manuscript, TeX, PDF, third-party dependencies, and cited literature are excluded from that grant.** See [LICENSE_SCOPE.md](LICENSE_SCOPE.md) and [PROVENANCE.md](PROVENANCE.md). Historical research reports, correspondence, proof-search materials, dependency checkouts, and third-party PDFs are not distributed.

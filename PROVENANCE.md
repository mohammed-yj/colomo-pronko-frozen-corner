# Provenance and publication boundary

The authoritative mathematical snapshot is the **final `colomo-pronko-submission` package**, comprising the main paper, its supplement, and the embedded `colomo-pronko-lean.zip`. The package directory and its enclosing submission ZIP agree byte for byte for all six payload files. The separate paper-only archive was also inventoried; no older manuscript is selected as authority.

The older publication-project manuscript and internal complete-proof/dependency reports are context only. The final Lean source is the submission ZIP's `colomo-pronko-lean/` tree. Its proof modules agree byte for byte with the earlier public-release tree, but its status files and stored historical build logs are not accepted as fresh evidence.

## Preserved and new material

[provenance.json](provenance.json) records the final archive hashes, source-relative origins, and SHA-256 hashes for **63 preserved files**: 59 Lean/configuration/tooling files and the four final paper/supplement PDF/TeX files. Every copied file is byte-identical to its selected authority. All 53 CP Lean modules (including the umbrella and explicit axiom report) are preserved. Existing tools retained are the official-frontend driver and the two declaration/dependency inspection modules; historical report-parsing scripts are replaced with clean audits of fresh output.

New release additions are the repository documentation, MIT scope, citation/configuration files, GitHub Actions, `tools/AllAxioms.lean`, the public source/dependency/axiom auditors, the transcription of supplement S.1 into `certificates/recurrence.json`, and the independent symbolic/matrix/counting checks. These are explicitly new reproducibility tools; they are not represented as recovered historical experiment scripts.

`certificates/fresh-lean-build.json` records the new local build command, environment, result, and every nonfatal warning. `certificates/lean-axioms.json` records the complete fresh project-theorem axiom inventory; CI regenerates that inventory from compiled proof terms and compares it exactly. The Python verification result and fixed ranges are recorded in `certificates/exact-verification.json`. These records describe checks, not new mathematical assumptions.

[SHA256SUMS](SHA256SUMS) is the explicit public file allowlist and hashes every published file except itself. `scripts/audit_sources.py` rejects missing/extra public files, changed preserved inputs, disallowed Lean tokens, unpinned dependencies, and common privacy artifacts. Only this clean repository directory is initialized as Git and staged for publication.

## Exclusions

Excluded: internal research/proof/dependency reports; continuation and recovery histories; adversarial or editorial reviews; old manuscript versions; proof-search artifacts; received/baseline status files; historical build/dependency logs; local inventory and source paths; editor/OS metadata; conversations and prompts; submission correspondence and account information; original ZIP containers and duplicate archives; `.lake/`, dependency checkouts, caches, Python bytecode, and temporary outputs; the locally supplied third-party CP/CP24 PDFs. External sources are cited by bibliographic links only.

The final manuscript's author, affiliation, and correspondence address are intentional publication metadata and remain unchanged. No local username or filesystem path is included in public content. PDF metadata was checked separately; the PDFs are the author's final materials and contain no JavaScript, forms, or embedded attachments.

## Nonblocking editorial observations

Appendix A prints an earlier supplement TeX filename; it denotes the final `paper/colomo-pronko-supplement.tex`. Some preserved Lean comments use earlier equation numbering and stage terminology. [PAPER_MAP.md](PAPER_MAP.md) provides the final mapping. The main and supplementary mathematical sources are not edited to resolve these presentation issues.

The final paper explicitly says historical finite ranges were not independently rerun and their full original scripts are unavailable. The new, fixed-range checks have their own commands and results; they neither validate that historical provenance nor replace the general proof.

# Depositing More Should Not Earn Less

Publication bundle: manuscript, figure sources and data,
reproducible analysis, and a Lean verification library.

- [Paper (PDF)](paper.pdf) and [LaTeX source](paper.tex); layout in `paperstyle.sty`.
- [Release report](verification/REPORT.md): results and verification limits.
- [Analysis](analysis/README.md): library, regression tests, frozen inputs and generators.
- [Formal verification](verification/REPORT.md): the `SupplierMonotonicity` proof library, its results and its limits.
- [Equation coverage](verification/COVERAGE.md) and [mathematical correspondence](verification/correspondence.md).
- [Recorded end-to-end result](verification/evidence/release.json).

## Reproduce

Install Python 3.12, [uv](https://docs.astral.sh/uv/), TeX Live (including Latin Modern,
amsmath, amsthm, booktabs, enumitem, microtype and hyperref), and
[elan](https://github.com/leanprover/elan). Put `lake`, `pdflatex` and `kpsewhich`
on PATH. Lean 4.24.0 and the exact mathlib revision are pinned in `verification/lean`.
The first run needs network access to fetch dependencies; dependencies are not
bundled. No external research folder, wallet or network service is used.

From this folder:

```sh
uv sync --project analysis --locked
cd verification/lean
lake exe cache get
cd ../..
uv run --project analysis --locked python reproduce.py
```

`lake exe cache get` retrieves mathlib's compiled cache. The proof checker then builds
the local proofs and audits every theorem's transitive axioms. The reproduction
command runs regression tests, regenerates all 22 figures and ten CSV files, checks
all 1,000,001 utilization ticks, runs formal/symbolic/numerical checks, and compiles
the PDF. Logs and source hashes are recorded in `verification/evidence`.
A failure replaces the end-to-end status with FAIL; PASS is not left over from an
older run. PDF metadata can vary between builds; source and numerical reproduction
are the relevant checks, not identical PDF bytes across dates or TeX installations.

To compile only the manuscript, run `pdflatex paper.tex` twice. For analysis only,
see `analysis/README.md`. All paths in the source are relative to this bundle.

## Verification boundary

The kernel checks the encoded Lean statements under their explicit assumptions.
The manuscript-to-Lean correspondence remains a human-readable review. The full
locally absolutely continuous / almost-everywhere admissible-family equivalence,
some global construction/regularity steps and integer transaction guarantees are
not fully formalized. This bundle does **not** certify every mathematical sentence
in the paper. Supporting lemmas, numerical checks and a paper theorem are different
units of evidence.

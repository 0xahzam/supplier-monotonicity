# Depositing More Should Not Earn Less

Ahzam Khan and Cavey Cool, September 2026.

Publication bundle: manuscript, figure sources and data,
reproducible analysis, and a Lean verification library.

- [Paper (PDF)](paper.pdf) and its [LaTeX source](build/main.tex), with layout in `build/paperstyle.sty`.
- [Analysis](analysis/README.md): library, regression tests, frozen inputs and generators.
- [Lean formalization](lean/README.md): the `SupplierMonotonicity` library, the paper results it proves and the ones still open.
- [Verification](verification/README.md): numerical, symbolic and integer-port checks, and the limits of each.
- [Equation coverage](verification/COVERAGE.md) and [mathematical correspondence](verification/correspondence.md).
- [Recorded end-to-end result](verification/evidence/release.json).

## Citation

```bibtex
@misc{khan2026depositing,
  author       = {Khan, Ahzam and Cool, Cavey},
  title        = {Depositing More Should Not Earn Less},
  year         = {2026},
  month        = sep,
  howpublished = {\url{https://github.com/0xahzam/supplier-monotonicity}}
}
```

## Reproduce

Install Python 3.12, [uv](https://docs.astral.sh/uv/), TeX Live (including Latin Modern,
amsmath, amsthm, booktabs, enumitem, microtype and hyperref), and
[elan](https://github.com/leanprover/elan). Put `lake`, `pdflatex` and `kpsewhich`
on PATH. Lean 4.24.0 and the exact mathlib revision are pinned in `lean/`.
The first run needs network access to fetch dependencies; dependencies are not
bundled. No external research folder, wallet or network service is used.

From this folder:

```sh
uv sync --project analysis --locked
cd lean
lake exe cache get
cd ..
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

To compile only the manuscript, run `pdflatex main.tex` twice from `build/`; that writes
`build/main.pdf`, and `reproduce.py` copies its own build to `paper.pdf`. For analysis only,
see `analysis/README.md`. All paths in the source are relative to this bundle.

## What is proved

Lean proves Propositions 1 and 6 and Theorems 3, 4 and 5, with Theorem 3 for rates that are
continuous and differentiable inside the interval. Not formalized: Theorem 2 in its locally
absolutely continuous form, boundary-curve uniqueness in Theorem 4, some global construction
steps, and rounded integer arithmetic. [lean/README.md](lean/README.md) has the table, and
[verification/COVERAGE.md](verification/COVERAGE.md) tracks each displayed equation.

## License

Apache License 2.0, covering the paper, figures, analysis code and Lean library. See
[LICENSE](LICENSE).

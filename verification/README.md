# Verification

This directory holds the checks that run alongside the Lean proofs, and the evidence they
record. The Lean library and the status of each paper result are in
[`../lean/README.md`](../lean/README.md).

## Running

From the repository root, after the setup in [`../README.md`](../README.md):

```sh
uv run --project analysis --locked python verification/check.py
```

`check.py` stops at the first failure and writes the step's log to `evidence/`. A passing run
writes [`evidence/verification.json`](evidence/verification.json) with the theorem count, the
axioms used, the number of rational comparisons and the SHA-256 of every input. If any input
changes during the run, it fails.

The root `reproduce.py` runs this script as one step. It also runs the analysis tests,
regenerates figures and data, checks the integer port and compiles the paper, and records the
result in [`evidence/release.json`](evidence/release.json).

## What each check does

| Check | What it verifies |
|---|---|
| Lean build and axiom audit | Builds `../lean`, rejects `sorry`, `admit`, `axiom`, `unsafe` and `native_decide` in the library, and accepts only `propext`, `Classical.choice` and `Quot.sound` in any theorem's transitive axioms. The `#print axioms` output is in `evidence/lean-axioms.log`. |
| Comparator statements | Every definition and statement in `../lean/ComparatorChallenges` matches the library text. |
| `numerical_audit.py` | Exact rational arithmetic and rational enclosures for numbers quoted in the paper, including an independent KKT reconstruction from the CSVs in `../analysis/data`. Writes `evidence/numerical-audit.json`. |
| `supplementary/*.py` | Symbolic, high-precision numerical, optimization and caption checks. Each script exits nonzero on any failed comparison. |
| `inventory.py` | Hashes every display and named theorem in `../build/main.tex` against `coverage-anchors.json` and regenerates `COVERAGE.md`. |
| Integer port | `../analysis/generate_market.py` compares all 1,000,001 integer utilization ticks with the continuous rational model and records the maximum APR difference, about `9.975×10⁻⁷`, in `../analysis/data/provenance.json`. `reproduce.py` fails if it reaches `10⁻⁶`. The guard sits at the claimed bound, so the margin is small. |

## Documents

- [`COVERAGE.md`](COVERAGE.md) gives every displayed equation and named result in the paper a
  status of proved, supported, definition or open, with the Lean declarations behind it.
  `inventory.py` generates it, so edit the table in `inventory.py`, not the Markdown.
- [`correspondence.md`](correspondence.md) maps the paper's notation to the Lean definitions
  and lists the assumptions each module adds.

## Scope

The Python scripts check specific numbers and identities from the paper. General claims are
proved in Lean.

The integer-port check covers the integer model in `../analysis`, not a deployed contract.

`coverage-anchors.json` stores a hash of each display and named result in `../build/main.tex`. If
the paper changes one, `inventory.py` fails until `COVERAGE.md` and the anchor are updated
together.

Regenerating the analysis is deterministic. The ten CSVs are byte-identical across runs and
the 22 figures render identically. SVG and PDF files embed a timestamp and per-run element ids,
so their bytes differ between runs.

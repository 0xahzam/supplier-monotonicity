# Publication verification report

This bundle contains the manuscript, the analysis that produces its figures and
data, and a Lean proof library for its mathematical claims. It runs standalone:
no external research repository, checkout or network service is required beyond
fetching pinned dependencies on first use. Exact results and source hashes are in
[evidence/release.json](evidence/release.json) and
[evidence/verification.json](evidence/verification.json).

## Evidence

- The analysis regression suite passes, including the smoothing-width and
  knot-side derivative cases.
- 105 Lean theorem declarations compile. Every theorem's transitive axiom
  dependencies are checked; only `propext`, `Classical.choice` and `Quot.sound`
  are used. No unfinished proof, added axiom or `native_decide` is accepted.
- 61 independent rational/enclosure comparisons pass. Separate symbolic,
  high-precision numerical, optimization and selected caption checks also run and
  fail the process on any recorded failed comparison. Individual counts are in
  `evidence/verification.json`.
- Every one of the 1,000,001 integer utilization ticks is checked against the
  continuous rational model. Maximum observed APR difference is approximately
  `9.975×10⁻⁷`, against a strict `<10⁻⁶` guard. This checks the included integer
  port, not execution or verification of any deployed program. The margin is
  small, so the guard is deliberately set at the claimed bound rather than above it.
- Regenerating the analysis is deterministic: the ten numerical CSVs are
  byte-identical and all 22 figures are pixel-identical across runs. Vector
  outputs additionally embed a generation timestamp and per-run element
  identifiers, so SVG and PDF files are not byte-identical between runs even
  though their rendered content is.
- The paper compiles with resolved references. The PDF and generated artifacts
  are hashed by the end-to-end reproduction command.

The supplementary scripts manually encode selected mathematical claims; they do
not read arbitrary LaTeX and prove it. The source inventory contains 58 displays,
six named theorems/propositions, 538 inline expressions, three tables and 25
captions. Counts are overlapping inventories, not certification counts. The
manuscript-to-Lean correspondence is a single human-readable review; it has not
been independently reproduced, and the proofs are checked by one kernel
implementation.

## What remains outside the formal certificate

The main open obligation is the admissible-family theorem at the paper's full
locally absolutely continuous / almost-everywhere regularity. Smooth derivative,
normalized-rate monotonicity and integral results are proved, but are not a
substitute for that general theorem. Other incomplete assembly steps include some
global boundary/repair existence and regularity claims, general rejoin/limit
arguments, and complete join regularity for constructed curves. The proof library
checks finite real-valued caps and continuous arithmetic; it does not prove
arbitrary rounded transaction monotonicity or the behavior of a deployed contract.

[COVERAGE.md](COVERAGE.md) records these distinctions expression by expression.
[correspondence.md](correspondence.md) records the assumptions and notation mapping.
A formalization gap is not a discovered mathematical counterexample. Conversely,
passing tests and numerical reproduction do not establish an unproved universal claim.

The defensible description is: **publication bundle with reproducible analysis and
substantial partial formal verification**, not "fully formally verified paper" or a
guarantee that no further mathematical issue exists.

## Running the checker

The single Lean package is `lean/SupplierMonotonicity`, pinned to Lean 4.24.0.
Project names and theorem namespaces describe the mathematics they encode.

Run from the bundle root, after installing dependencies described in `../README.md`:

```sh
uv run --project analysis --locked python verification/check.py
```

The checker builds the library, generates `lean/Audit.lean`, inspects every theorem's
transitive axiom dependencies, runs the independent rational audit and five
supplementary suites, and validates the source inventory. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. No `sorry`, custom axioms or
`native_decide` escape hatch is permitted in the local proof source.

`coverage-anchors.json` pins the reviewed display/theorem texts in their source
order. Changing one forces a correspondence review before updating those anchors;
blindly regenerating them would defeat the guard. Inline math and prose are indexed,
not individually certified. `COVERAGE.md` distinguishes proofs, supporting components,
definitions and open obligations. See `correspondence.md` for domain assumptions.

The numerical and symbolic scripts are complementary evidence, not Lean proofs.
Their parameters were manually transcribed and checked against the manuscript;
they are not a semantic LaTeX parser. The rational audit checks exact arithmetic
and rational enclosures, including a separate KKT reconstruction from CSV data.
The supplementary scripts fail the process if any recorded check fails.

Use the root `reproduce.py` command to also test the analysis, regenerate figures,
check the integer port and compile the paper. `evidence/verification.json` alone
reports this mathematical checker, not the whole build.

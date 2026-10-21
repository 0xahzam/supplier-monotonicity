# Comparator challenges

[`SupplierMonotonicity.lean`](SupplierMonotonicity.lean) contains the paper's main results as
statements with `sorry` proofs, plus the definitions they use. It imports only Mathlib, so you
can review what is claimed without reading any proof.

[Comparator](https://github.com/leanprover/comparator) checks that `SupplierMonotonicity.Main`
proves exactly these statements and uses no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`. The configuration is [`SupplierMonotonicity.json`](SupplierMonotonicity.json).

## Running Comparator

Comparator needs `comparator`, `landrun` and `lean4export` on `PATH`. `landrun` uses Linux
Landlock, so this step runs on Linux only. From `lean/`:

```sh
lake exe cache get
lake build
lake env comparator ComparatorChallenges/SupplierMonotonicity.json
```

## Without Comparator

`verification/check.py` runs on any platform. It builds the challenge file, checks that every
definition and statement in it matches the library text exactly (ignoring whitespace), and audits
the axioms of every theorem with `#print axioms`. The text match is weaker than Comparator's
kernel-level comparison, but it fails if anyone edits a statement in one place and not the other.

## Editing a statement

Change the theorem in `SupplierMonotonicity/Main.lean` first, then copy the same statement into
the challenge file. The checker rejects the build until both agree.

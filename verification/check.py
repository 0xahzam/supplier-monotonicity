#!/usr/bin/env python3
"""Build the canonical proof library and run the complementary verification suites."""

import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / "lean"
EVIDENCE = ROOT / "evidence"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, command, cwd=ROOT):
    """Run a step. Output is kept only when the step fails, so a passing run
    leaves no transient logs behind; results live in verification.json."""
    result = subprocess.run(
        command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    if result.returncode:
        (EVIDENCE / f"{label}.log").write_text(result.stdout)
        raise RuntimeError(f"{label} failed; see verification/evidence/{label}.log")
    print(f"{label}: PASS", flush=True)
    return result.stdout


def main():
    EVIDENCE.mkdir(exist_ok=True)
    status_path = EVIDENCE / "verification.json"
    status_path.write_text(json.dumps({"status": "RUNNING", "whole_paper_certified": False}) + "\n")
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("lake not found: install elan and put its bin directory on PATH")
    proof_files = sorted((LEAN / "SupplierMonotonicity").glob("*.lean"))
    source = "\n".join(p.read_text() for p in proof_files)
    names = re.findall(r"^theorem\s+(\w+)", source, re.MULTILINE)
    if len(names) != len(set(names)):
        raise RuntimeError("Duplicate theorem names")
    uncommented = re.sub(r"/-.*?-/|--[^\n]*", "", source, flags=re.DOTALL)
    if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", uncommented):
        raise RuntimeError("Proof escape hatch found in project sources")
    (LEAN / "Audit.lean").write_text(
        "import SupplierMonotonicity\n\n"
        + "\n".join(f"#print axioms SupplierMonotonicity.{name}" for name in names)
        + "\n"
    )
    inputs = [
        ROOT.parent / "paper.tex",
        *proof_files,
        LEAN / "SupplierMonotonicity.lean",
        LEAN / "Audit.lean",
        LEAN / "lakefile.toml",
        LEAN / "lake-manifest.json",
        LEAN / "lean-toolchain",
        ROOT / "coverage-anchors.json",
        *ROOT.glob("*.py"),
        *ROOT.glob("supplementary/*.py"),
        *ROOT.parent.glob("analysis/data/*.csv"),
    ]
    before = {str(p.relative_to(ROOT.parent)): digest(p) for p in inputs}
    run("lean-build", [lake, "build"], LEAN)
    output = run("lean-axioms", [lake, "env", "lean", "Audit.lean"], LEAN)
    (EVIDENCE / "lean-axioms.log").write_text(output)
    axiom_sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
    empty = len(re.findall(r"does not depend on any axioms", output))
    if len(axiom_sets) + empty != len(names):
        raise RuntimeError("Axiom audit did not cover every theorem")
    used = {n.strip() for group in axiom_sets for n in group.split(",") if n.strip()}
    if not used <= {"propext", "Classical.choice", "Quot.sound"}:
        raise RuntimeError(f"Unexpected axioms: {used}")
    run("rational-numerics", [sys.executable, str(ROOT / "numerical_audit.py")])
    numerics = json.loads((EVIDENCE / "numerical-audit.json").read_text())
    if numerics["out_of_tolerance"]:
        raise RuntimeError("Independent rational comparisons outside tolerances")
    supplementary = {}
    for script in sorted((ROOT / "supplementary").glob("*.py")):
        out = run(script.stem, [sys.executable, str(script)])
        supplementary[script.stem] = {
            "status": "PASS",
            "summary": out.strip().splitlines()[-1],
        }
    run("inventory", [sys.executable, str(ROOT / "inventory.py")])
    after = {str(p.relative_to(ROOT.parent)): digest(p) for p in inputs}
    if before != after:
        raise RuntimeError("Verification inputs changed during this run")
    status = {
        "status": "PASS",
        "whole_paper_certified": False,
        "scope": "Encoded theorems, independent arithmetic and selected caption checks; see COVERAGE.md for unproved obligations.",
        "theorem_count": len(names),
        "theorems": names,
        "axioms": sorted(used),
        "toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "manuscript_sha256": digest(ROOT.parent / "paper.tex"),
        "rational_comparisons": len(numerics["checks"]),
        "supplementary": supplementary,
        "input_sha256": before,
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    print(
        f"PASS: {len(names)} Lean theorems; standard axioms only; {len(numerics['checks'])} rational comparisons."
    )


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        EVIDENCE.mkdir(exist_ok=True)
        (EVIDENCE / "verification.json").write_text(
            json.dumps(
                {
                    "status": "FAIL",
                    "whole_paper_certified": False,
                    "reason": str(error),
                },
                indent=2,
            )
            + "\n"
        )
        print(str(error), file=sys.stderr)
        sys.exit(1)

#!/usr/bin/env python3
"""Rebuild analysis, figures, formal evidence and the paper from this directory.

Run with `uv run --project analysis --locked python reproduce.py` after putting
elan's lake and TeX Live's pdflatex/kpsewhich on PATH.
"""

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "verification/evidence"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, command, cwd, env):
    print(f"{label} …", flush=True)
    result = subprocess.run(
        command,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        (EVIDENCE / f"{label}.log").write_text(result.stdout)
        raise RuntimeError(f"{label} failed; see verification/evidence/{label}.log")
    return result.stdout


def main():
    EVIDENCE.mkdir(exist_ok=True)
    (EVIDENCE / "release.json").write_text('{"status":"RUNNING"}\n')
    for command in ["lake", "pdflatex", "kpsewhich"]:
        if not shutil.which(command):
            raise RuntimeError(f"{command} is required; see README.md")
    inputs = [
        ROOT / "build/main.tex",
        ROOT / "build/paperstyle.sty",
        ROOT / "reproduce.py",
        *sorted((ROOT / "analysis").rglob("*.py")),
        ROOT / "analysis/pyproject.toml",
        ROOT / "analysis/uv.lock",
        ROOT / "analysis/config/market.json",
    ]
    inputs = [p for p in inputs if not any(x in p.parts for x in [".venv", ".lake", "__pycache__"])]
    before = {str(p.relative_to(ROOT)): sha256(p) for p in inputs}
    env = os.environ.copy()
    # Never pollute the source bundle with font caches or bytecode.
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    with tempfile.TemporaryDirectory(prefix="paper-figures-") as cache:
        env["MPLCONFIGDIR"] = cache
        tests = run(
            "python-tests",
            [sys.executable, "-m", "pytest", "tests", "-q", "-p", "no:cacheprovider"],
            ROOT / "analysis",
            env,
        )
        run(
            "figure-generation",
            [sys.executable, "generate_figures.py"],
            ROOT / "analysis",
            env,
        )
    run("verification", [sys.executable, "verification/check.py"], ROOT, env)
    # Compile from build/ into a scratch directory so no LaTeX artefacts land in the bundle.
    with tempfile.TemporaryDirectory(prefix="paper-latex-") as out:
        for n in range(1, 4):
            latex = run(
                f"latex-pass{n}",
                [
                    "pdflatex",
                    "-interaction=nonstopmode",
                    "-halt-on-error",
                    f"-output-directory={out}",
                    "main.tex",
                ],
                ROOT / "build",
                env,
            )
        shutil.copyfile(Path(out) / "main.pdf", ROOT / "paper.pdf")
    if re.search(
        r"undefined references|undefined citations|Rerun to get|Overfull \\[hv]box",
        latex,
    ):
        raise RuntimeError(
            "Unresolved LaTeX references or overflowing boxes; inspect latex-pass3.log"
        )
    figures = re.findall(
        r"\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}", (ROOT / "build/main.tex").read_text()
    )
    if len(figures) != 20 or any(not (ROOT / "figures" / name).is_file() for name in figures):
        raise RuntimeError("Paper figure inventory does not match 20 generated figures")
    if before != {str(p.relative_to(ROOT)): sha256(p) for p in inputs}:
        raise RuntimeError("Release sources changed during reproduction")
    proof = json.loads((EVIDENCE / "verification.json").read_text())
    data = json.loads((ROOT / "analysis/data/provenance.json").read_text())
    if proof["status"] != "PASS" or data["integer_rational_max_apr_error"] >= 1e-6:
        raise RuntimeError("Verification or integer error bound failed")
    status = {
        "status": "PASS",
        "whole_paper_certified": False,
        "paper_sha256": sha256(ROOT / "build/main.tex"),
        "pdf_sha256": sha256(ROOT / "paper.pdf"),
        "python_tests": re.findall(r"\d+ passed", tests)[-1],
        "lean_theorems": proof["theorem_count"],
        "rational_comparisons": proof["rational_comparisons"],
        "figure_count": len(figures),
        "integer_ticks_checked": 1000001,
        "integer_max_apr_error": data["integer_rational_max_apr_error"],
        "input_sha256": before,
        "output_sha256": {
            str(p.relative_to(ROOT)): sha256(p)
            for p in [
                *sorted((ROOT / "analysis/data").glob("*")),
                *sorted((ROOT / "figures").glob("*.pdf")),
                ROOT / "verification/evidence/verification.json",
            ]
        },
    }
    (EVIDENCE / "release.json").write_text(json.dumps(status, indent=2) + "\n")
    print(
        f"PASS: {status['python_tests']}; {status['lean_theorems']} Lean theorems; 20 figures; paper.pdf rebuilt."
    )


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        EVIDENCE.mkdir(exist_ok=True)
        (EVIDENCE / "release.json").write_text(
            json.dumps({"status": "FAIL", "reason": str(error)}, indent=2) + "\n"
        )
        print(str(error), file=sys.stderr)
        sys.exit(1)

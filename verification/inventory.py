#!/usr/bin/env python3
"""Index literal source spans. Indexing is not proof or semantic claim extraction."""

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "build" / "main.tex"

# Status applies to the displayed expression, not automatically to nearby prose.
# 'supported' means checked components exist, but the full paper statement has
# remaining assembly, regularity, existence or correspondence obligations.
COVERAGE = {
    1: ("definition", "Supply-rate definition; algebraic substitution U=B/T."),
    2: ("definition", "Income model, encoded in Model.income."),
    3: ("definition", "Resulting share, encoded in Model.share."),
    4: ("proved", "utilization_hasDerivAt; smooth deposit path."),
    5: ("proved", "income_hasDerivAt_raw and income_hasDerivAt."),
    6: ("proved", "income_hasDerivAt / income_deriv."),
    7: ("proved", "logarithmic_elasticity: derivative of log(R(exp x))."),
    8: ("proved", "income_deriv."),
    9: ("proved", "income_deriv_nonneg_iff."),
    10: ("proved", "income_deriv_safe_share_iff; interior utilization."),
    11: ("proved", "full_supplier_deriv."),
    12: ("proved", "profile_all_shares_iff and envelope_iff, applied pointwise."),
    13: (
        "supported",
        "logarithmic_elasticity and envelope_iff; normalized_rate_antitone and normalized_rate_bound establish the smooth boundary-ratio implication. General AC/a.e. integration remains open.",
    ),
    14: ("open", "Locally absolutely continuous / a.e. admissible-family theorem not formalized."),
    15: (
        "definition",
        "Fixed protection target definition; envelope_iff gives its pointwise consequence.",
    ),
    16: ("proved", "power_boundary_derivative, power_boundary_elasticity, power_exp_matches_rpow."),
    17: (
        "supported",
        "log_rate_integral_on proves smooth-interior log-rate FTC with integrability; full AC regularity remains open.",
    ),
    18: (
        "supported",
        "smooth_endpoint_bound and power_hits_top; AC essential-supremum version remains open.",
    ),
    19: (
        "supported",
        "safe_share_iff plus endpoint bound in smooth subclass; general endpoint theorem pending.",
    ),
    20: ("definition", "Initial/final utilization; nonzero denominators made explicit."),
    21: ("proved", "fresh_share."),
    22: ("proved", "fresh_path_iff."),
    23: (
        "supported",
        "fresh_all_starts_iff and fresh_share; explicit realization of every worst-case state not separately encoded.",
    ),
    24: ("proved", "fresh_envelope and fresh_envelope_iff."),
    25: (
        "supported",
        "hyperbolic_boundary_derivative and hyperbolic_boundary_elasticity; integrated uniqueness pending.",
    ),
    26: (
        "supported",
        "fresh_base_positive checks consequence of bound; normalized_base_bound checks antitone endpoint step. Full limit argument pending.",
    ),
    27: ("definition", "Slope between distinct kinks."),
    28: (
        "proved",
        "fresh_linear_segment_iff and adjacent_fresh_ratio_iff; positive left rate and increasing kinks.",
    ),
    29: ("definition", "Single-kink baseline; numerical endpoints checked."),
    30: (
        "supported",
        "Exact rational sign bracket for quoted K=19 root; general root existence/uniqueness pending.",
    ),
    31: (
        "supported",
        "Power branch elasticity and endpoint checks proved; full rejoin/greatest-minorant theorem pending.",
    ),
    32: ("proved", "max_profile_envelope and combined_envelope; positive profiles."),
    33: (
        "supported",
        "raise_recursion_minimal and raise_step_feasible; reverse indexing explicit; finite caps.",
    ),
    34: ("definition", "Accumulated interest for integrable prescribed histories."),
    35: (
        "proved",
        "accumulated_interest_difference and supplier_transfer; integrability explicit.",
    ),
    36: ("definition", "Affine rate and elasticity substitution; endpoint theorem below."),
    37: (
        "proved",
        "integer_endpoint_iff; fixed_linear_endpoint_suffices; continuous arithmetic, not rounded transactions.",
    ),
    38: ("proved", "fresh_boundary_income_algebra together with Core derivative and fresh share."),
    39: ("proved", "adjacent_fresh_ratio_iff."),
    40: (
        "proved",
        "fixed_left_cap_iff, fixed_right_cap_iff, fixed_right_unbounded, fixed_left_zero, combined_envelope.",
    ),
    41: (
        "supported",
        "floor_recursion_minimal; unbounded-cap limit handled numerically, not encoded in recursion theorem.",
    ),
    42: (
        "supported",
        "lower_recursion_maximal; complete constructed-curve feasibility not yet assembled.",
    ),
    43: (
        "scope qualification",
        "Normalized derivative equivalence, smooth antitonicity, running-infimum antitonicity and order bounds proved. The paper now assumes positive base rate; zero_base_flat_minorant explains why an unrestricted assertion is false. Continuity/regularity still pending.",
    ),
    44: (
        "supported",
        "Power and hyperbolic branches checked separately; combined join, regularity and general K>0 domain not assembled.",
    ),
    45: (
        "supported",
        "normalized_base_bound plus exact numerical check for K=19; general combined construction attainment pending.",
    ),
    46: (
        "supported",
        "reconstructedRate_* proves positive C1 construction for continuous log-coordinate elasticity; reconstructed_utilization_elasticity gives eta. General local-profile extension, change of variables and full converse pending.",
    ),
    47: (
        "proved",
        "continuous_rate_supremum_strict: positive continuous rate, interior differentiability, continuous derivative/rate quotient, and endpoint budget; explicit C1-data convention in Smoothing.lean.",
    ),
    48: ("definition", "smoothEta; continuity and exact integral formally proved for w>0."),
    49: (
        "proved",
        "smoothing_endpoint_unique for w>0; smooth_zero_width for the declared limiting value.",
    ),
    50: ("proved", "smooth_plateau_derivative and smooth_plateau_derivative_positive."),
    51: (
        "proved",
        "smoothing_ceiling_width_iff: full pointwise ceiling for w>0 and eta0<Kstar; w=0 is the separately declared limiting value.",
    ),
    52: ("proved", "smoothEta_integral and smooth_area_identity. Corrected smoothing identity."),
    53: (
        "supported",
        "smooth_ramp_primitive_derivative, smooth_primitive_join and reconstructedRate_*; C2 join assembly pending.",
    ),
}

THEOREMS = {
    1: ("proved", "Core derivative theorem at smooth states."),
    2: (
        "open",
        "Full a.e. / locally absolutely continuous equivalence pending; no replacement by smooth result.",
    ),
    3: (
        "supported",
        "Smooth endpoint bound and power attainment proved; AC essential-supremum theorem pending.",
    ),
    4: (
        "supported",
        "Worst start, pointwise envelope, boundary derivative and finite-deposit lemmas proved; full theorem assembly and boundary uniqueness pending.",
    ),
    5: (
        "supported",
        "Strict supremum statement proved directly in U using explicit C1 data; positive C1 reconstruction and width existence proved. Full assembled feasibility including all interval/join assumptions pending.",
    ),
    6: (
        "proved",
        "Exact integral, plateau uniqueness, derivative, strictness and pointwise ceiling-width equivalence for nonzero width; zero width handled as the stated nonsmooth limit.",
    ),
}


def main():
    text = SOURCE.read_text()
    items = []
    anchors = json.loads((ROOT / "coverage-anchors.json").read_text())
    spans = [
        m.group()
        for m in re.finditer(
            r"\\\[.*?\\\]|\\begin\{equation\}.*?\\end\{equation\}", text, re.DOTALL
        )
    ]
    statements = [
        m.group()
        for m in re.finditer(r"\\begin\{(theorem|proposition)\}.*?\\end\{\1\}", text, re.DOTALL)
    ]
    actual = {
        "displays": [hashlib.sha256(x.encode()).hexdigest() for x in spans],
        "statements": [hashlib.sha256(x.encode()).hexdigest() for x in statements],
    }
    if actual != anchors:
        raise RuntimeError(
            "Equation/theorem text changed: review correspondence and coverage anchors before certifying this revision"
        )

    def add(kind, prefix, spans):
        for n, (start, end) in enumerate(spans, 1):
            row = {
                "id": f"{prefix}{n:03d}",
                "kind": kind,
                "line_start": text.count("\n", 0, start) + 1,
                "line_end": text.count("\n", 0, end) + 1,
                "verbatim": text[start:end],
                "status": "indexed",
                "evidence": "",
            }
            if prefix == "D":
                row["status"], row["evidence"] = COVERAGE[n]
            if prefix == "T":
                row["status"], row["evidence"] = THEOREMS[n]
            items.append(row)

    add(
        "display",
        "D",
        [
            (m.start(), m.end())
            for m in re.finditer(
                r"\\\[.*?\\\]|\\begin\{equation\}.*?\\end\{equation\}", text, re.DOTALL
            )
        ],
    )
    add(
        "inline",
        "I",
        [
            (m.start(), m.end())
            for m in re.finditer(r"(?<!\\)\$(?!\$).*?(?<!\\)\$", text, re.DOTALL)
        ],
    )
    add(
        "theorem/proposition",
        "T",
        [
            (m.start(), m.end())
            for m in re.finditer(r"\\begin\{(theorem|proposition)\}.*?\\end\{\1\}", text, re.DOTALL)
        ],
    )
    add(
        "table",
        "B",
        [
            (m.start(), m.end())
            for m in re.finditer(r"\\begin\{table\}.*?\\end\{table\}", text, re.DOTALL)
        ],
    )
    captions = []
    for m in re.finditer(r"\\caption\{", text):
        depth = 1
        i = m.end()
        while depth:
            if text[i] in "{}" and text[i - 1] != "\\":
                depth += 1 if text[i] == "{" else -1
            i += 1
        captions.append((m.start(), i))
    add("caption", "C", captions)
    # Conservatively index all body blocks, including proofs and text without $.
    # This avoids losing prose assertions merely because they have no math delimiter.
    start = text.index("\\begin{abstract}")
    add(
        "source block",
        "P",
        [
            (start + m.start(), start + m.end())
            for m in re.finditer(r"\S(?:.*?\S)?(?=\n\s*\n|\Z)", text[start:], re.DOTALL)
        ],
    )
    counts = {k: sum(x["kind"] == k for x in items) for k in sorted({x["kind"] for x in items})}
    rows = [
        "# Equation and theorem coverage",
        "",
        "Reference: `../build/main.tex`. **Proved** means a Lean theorem states the claim. **Supported** means Lean proves parts of the claim and the entry names the missing step. **Open** means the claim is not formalized. **Definition** marks a model input.",
        "",
        "| ID | Source line | Status | Evidence / remaining obligation |",
        "|---|---:|---|---|",
    ]
    for item in items:
        if item["kind"] in ("display", "theorem/proposition"):
            rows.append(
                f"| {item['id']} | {item['line_start']} | {item['status']} | {item['evidence']} |"
            )
    rows += [
        "",
        "Inline fragments, captions, tables and source blocks are hashed and counted but have no individual status.",
        "",
        f"Inventory counts (overlapping): `{counts}`.",
        "",
    ]
    (ROOT / "COVERAGE.md").write_text("\n".join(rows))
    print(counts)


if __name__ == "__main__":
    main()

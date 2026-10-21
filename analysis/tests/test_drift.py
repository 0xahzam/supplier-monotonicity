"""Checks on the Drift evidence: the rate curve rules, and the published results.

The curve checks use hand computed values. The result checks pin the numbers the paper
prints, so a change to the analysis cannot move them silently.
"""

from __future__ import annotations

from pathlib import Path

import pytest
from supplier_monotonicity.drift import knots, rate_and_slope, run

DATA = Path(__file__).resolve().parents[1] / "data/drift"


def test_single_kink_curve():
    pts = knots(800_000, 50_000, 1_000_000, segmented=False)
    assert pts == [(0.0, 0.0), (0.8, 0.05), (1.0, 1.0)]
    rate, slope = rate_and_slope(0.83, pts)
    assert rate == pytest.approx(0.1925)
    assert slope == pytest.approx(4.75)


def test_segmented_curve_reaches_maximum():
    pts = knots(800_000, 52_500, 900_000, segmented=True)
    assert pts[-1] == (1.0, pytest.approx(0.9))
    # From the 85% breakpoint on, the weights 50, 100, 150, 200, 250, 250 split the range.
    assert pts[2] == (0.85, pytest.approx(0.0525 + 0.8475 * 0.05))


def test_slope_at_a_kink_is_the_one_below():
    pts = knots(800_000, 50_000, 1_000_000, segmented=False)
    _, slope = rate_and_slope(0.8, pts)
    assert slope == pytest.approx(0.05 / 0.8)


@pytest.fixture(scope="module")
def summary():
    return run(DATA)


@pytest.mark.parametrize("market", ["SOL", "USDC"])
def test_curve_matches_accrued_interest(summary, market):
    fit = summary[market]["fit"]
    assert fit["above_kink"] < 0.01
    assert fit["below_kink"] < 0.01


@pytest.mark.parametrize(
    ("market", "lender", "any_supplier"), [("SOL", 0.114, 0.114), ("USDC", 0.079, 0.116)]
)
def test_exposed_hours(summary, market, lender, any_supplier):
    s = summary[market]["suppliers"]
    assert s["exposed_hours_lender"] == pytest.approx(lender, abs=5e-4)
    assert s["exposed_hours_any"] == pytest.approx(any_supplier, abs=5e-4)
    # Lenders are a subset of all suppliers, so their exposed hours cannot exceed the total.
    assert s["exposed_hours_lender"] <= s["exposed_hours_any"]

"""Checks on the proposed curve itself."""

import pytest
from supplier_monotonicity.proposal import (
    Kink,
    elasticity_of,
    feasible,
    income,
    new_rate,
    old_rate,
    power_rate,
    rejoin,
)

CURVES = [
    Kink(0.80, 0.0525, 0.90),  # USDT
    Kink(0.80, 0.1000, 1.50),  # SOL
    Kink(0.75, 0.0600, 1.50),  # wBTC / wETH
    Kink(0.90, 0.0200, 2.00),  # a deliberately steep one
]
KS = [19.0, 30.0, 60.0]


def pairs(ks=KS):
    return [(c, k) for c in CURVES for k in ks if feasible(c, k)]


@pytest.mark.parametrize("c", CURVES)
def test_peak_elasticity_closed_form(c):
    """The kink is the worst point, and its elasticity is O·m/R_o."""
    just_above = c.optimal_utilization + 1e-9
    numeric = elasticity_of(just_above, lambda u: old_rate(u, c), h=1e-10)
    assert numeric == pytest.approx(c.peak_elasticity, rel=1e-4)
    for u in (0.85, 0.9, 0.95, 0.999):
        assert elasticity_of(u, lambda x: old_rate(x, c)) < c.peak_elasticity


@pytest.mark.parametrize("c", CURVES)
def test_k_star_is_where_the_power_curve_lands_on_r_max(c):
    """K* is defined by R_o·(1/O)^K* = R_max."""
    assert power_rate(1.0, c, c.k_star) == pytest.approx(c.max_rate, rel=1e-9)
    assert not feasible(c, c.k_star * 0.99)
    assert feasible(c, c.k_star * 1.01)


@pytest.mark.parametrize("c,k", pairs())
def test_new_curve_is_continuous(c, k):
    """No jump at the kink or at the rejoin point."""
    u_c = rejoin(c, k)
    o = c.optimal_utilization
    for u in (o, u_c):
        lo = new_rate(u - 1e-7, c, k, u_c)
        hi = new_rate(u + 1e-7, c, k, u_c)
        assert lo == pytest.approx(hi, rel=1e-4, abs=1e-7)


@pytest.mark.parametrize("c,k", pairs())
def test_new_curve_never_exceeds_the_elasticity_ceiling(c, k):
    """η ≤ K everywhere, which is the whole claim."""
    u_c = rejoin(c, k)
    us = [i / 4000 for i in range(1, 4001)]
    for u in us:
        if abs(u - c.optimal_utilization) < 1e-3 or abs(u - u_c) < 1e-3:
            continue  # skip the slope discontinuities themselves
        assert elasticity_of(u, lambda x: new_rate(x, c, k, u_c)) <= k * 1.001


@pytest.mark.parametrize("c,k", pairs())
def test_new_curve_is_below_old_inside_the_replaced_span_and_equal_outside(c, k):
    u_c = rejoin(c, k)
    o = c.optimal_utilization
    if u_c > o + 1e-6:
        mid = (o + u_c) / 2
        assert new_rate(mid, c, k, u_c) < old_rate(mid, c)
    for u in (o * 0.5, o, min(u_c + 1e-6, 1.0), 1.0):
        assert new_rate(u, c, k, u_c) == pytest.approx(old_rate(u, c), rel=1e-6)


@pytest.mark.parametrize("c,k", pairs())
def test_max_rate_is_untouched(c, k):
    assert new_rate(1.0, c, k, rejoin(c, k)) == pytest.approx(c.max_rate, rel=1e-9)


@pytest.mark.parametrize("c,k", pairs())
def test_protected_supplier_never_loses_by_depositing(c, k):
    """A supplier ending at or under 1/(1+K) sees income rise, never fall."""
    u_c = rejoin(c, k)
    fn = lambda u: new_rate(u, c, k, u_c)
    alpha_bar = 1 / (1 + k)
    total = 10_000_000.0
    for u0 in (c.optimal_utilization + 0.005, (c.optimal_utilization + u_c) / 2, 0.97):
        borrowed = total * u0
        d_max = max(borrowed / c.optimal_utilization - total, 0.0)
        if d_max <= 0:
            continue
        b0 = alpha_bar * (total + d_max) - d_max
        if b0 <= 0:
            continue
        ys = [income(d_max * i / 300, b0 / total, total, borrowed, fn) for i in range(301)]
        assert all(b >= a - 1e-9 for a, b in zip(ys, ys[1:]))


@pytest.mark.parametrize("c", CURVES)
def test_large_k_collapses_onto_the_current_curve(c):
    """ᾱ → 0 means K → ∞, and the proposal falls back to the existing model."""
    k = c.peak_elasticity * 1.0001
    assert rejoin(c, k) == pytest.approx(c.optimal_utilization, abs=1e-3)
    for u in (0.85, 0.92, 0.99):
        assert new_rate(u, c, k) == pytest.approx(old_rate(u, c), rel=1e-6)

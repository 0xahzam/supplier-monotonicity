"""Verification of the elasticity result against the real onchain curve."""

from fractions import Fraction as F

import pytest
from supplier_monotonicity import (
    PRECISION,
    borrow_rate,
    borrow_rate_int,
    breakpoints,
    elasticity,
    income,
    income_derivative,
    load_markets,
    max_elasticity,
    minimum_feasible_elasticity,
    violations,
)
from supplier_monotonicity.elasticity import segment_elasticity

MARKETS = load_markets()
ALPHAS = [F(1, 200), F(1, 100), F(1, 50), F(1, 20), F(1, 10), F(1, 5)]


def deriv(alpha, total, borrowed, pts, h=F(1, 10**6)):
    """Exact central difference of income in the added deposit."""
    hi = income(h, alpha, total, borrowed, pts)
    lo = income(-h, alpha, total, borrowed, pts)
    return (hi - lo) / (2 * h)


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
@pytest.mark.parametrize("alpha", ALPHAS, ids=lambda a: f"a{float(a):.3f}")
@pytest.mark.parametrize("util", [700_000, 850_000, 930_000, 970_000, 993_000])
def test_income_derivative_matches_closed_form(m, alpha, util):
    """dI/d_delta == U * R_b(U) * [1 - alpha * (1 + eta)], exactly.

    Left side comes from the product and chain rules with no elasticity in it,
    so this tests the rearrangement in the article, not a tautology.
    """
    pts = breakpoints(m)
    total = F(10**9)
    borrowed = total * util // PRECISION
    u = F(util)
    expected = (
        (u / PRECISION) * (borrow_rate(u, pts) / PRECISION) * (1 - alpha * (1 + elasticity(u, pts)))
    )
    assert income_derivative(alpha, total, borrowed, pts) == expected


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
@pytest.mark.parametrize("util", [700_000, 930_000, 970_000, 993_000])
def test_finite_difference_converges_to_the_analytic_derivative(m, util):
    """Numeric slope of income converges quadratically on the closed form.

    A central difference is never exactly equal for a non-quadratic, so the
    check is on the convergence order rather than on equality.
    """
    pts = breakpoints(m)
    total = F(10**9)
    borrowed = total * util // PRECISION
    alpha = F(1, 20)
    exact = income_derivative(alpha, total, borrowed, pts)
    errs = [abs(deriv(alpha, total, borrowed, pts, F(1, 10**k)) - exact) for k in (2, 3, 4)]
    assert all(e > 0 for e in errs)
    for a, b in zip(errs, errs[1:]):
        assert 50 < a / b < 200  # ~100x per 10x step, i.e. second order


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
@pytest.mark.parametrize("util", [850_001, 930_000, 970_000, 993_000, 999_000])
def test_alpha_safe_is_the_exact_sign_flip(m, util):
    """Income rises below 1/(1+eta), is stationary at it, falls above it."""
    pts = breakpoints(m)
    total, borrowed = F(10**9), F(10**9) * util // PRECISION
    eta = elasticity(F(util), pts)
    if eta == 0:
        pytest.skip("flat region, every supplier protected")
    a = 1 / (1 + eta)
    assert income_derivative(a * F(999, 1000), total, borrowed, pts) > 0
    assert income_derivative(a, total, borrowed, pts) == 0
    assert income_derivative(a * F(1001, 1000), total, borrowed, pts) < 0


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
def test_elasticity_is_monotone_across_each_linear_segment(m):
    """eta' has the sign of the intercept c = r - m*u, so endpoints bound eta."""
    pts = breakpoints(m)
    for i in range(len(pts) - 1):
        (u0, r0), (u1, r1) = pts[i], pts[i + 1]
        if u1 == u0 or r1 == r0 or u0 == 0:
            continue
        slope = (r1 - r0) / (u1 - u0)
        intercept = r0 - slope * u0
        samples = [segment_elasticity(u0 + (u1 - u0) * F(k, 32), pts, i) for k in range(33)]
        pairs = list(zip(samples, samples[1:]))
        if intercept > 0:
            assert all(a <= b for a, b in pairs)
        else:
            assert all(a >= b for a, b in pairs)
        assert max(samples) == max(samples[0], samples[-1])


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
@pytest.mark.parametrize("k", [5, 10, 19, 50, 99, 110])
def test_division_free_check_agrees_with_eta_le_k(m, k):
    """U*dr <= K*r*dU on both endpoints is exactly eta <= K on the segment."""
    pts = breakpoints(m)
    by_eta = all(
        max(segment_elasticity(pts[i][0], pts, i), segment_elasticity(pts[i + 1][0], pts, i)) <= k
        for i in range(len(pts) - 1)
        if pts[i + 1][0] != pts[i][0] and pts[i + 1][1] != pts[i][1] and pts[i][0] != 0
    )
    assert by_eta == (violations(pts, k) == [])


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
def test_integer_port_matches_rational_model(m):
    """The Fraction model reproduces the onchain integer curve to rounding."""
    pts = breakpoints(m)
    worst = max(
        abs(borrow_rate_int(u, m) - borrow_rate(F(u), pts)) for u in range(0, PRECISION + 1, 251)
    )
    assert worst <= 2


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
def test_elasticity_is_one_below_optimal_utilization(m):
    """Below the kink the rate is proportional to U, so eta is exactly 1."""
    pts = breakpoints(m)
    floor_end = max((u for u, r in pts if r == F(m.floor)), default=F(0))
    for u in (floor_end + 1000, F(m.optimal_utilization) - 1):
        if u <= floor_end:
            continue
        assert elasticity(u, pts) == 1


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
def test_max_elasticity_exceeds_the_endpoint_lower_bound(m):
    """Realised eta is at least K*, the floor the endpoints already force."""
    eta, _ = max_elasticity(breakpoints(m))
    assert float(eta) >= minimum_feasible_elasticity(m)


def test_discrete_deposit_can_lose_money():
    """The infinitesimal condition shows up as a real loss on a real deposit."""
    m = next(x for x in MARKETS if x.name == "USDT")
    pts = breakpoints(m)
    total, borrowed = F(10**9), F(99 * 10**7)
    alpha = F(1, 4)
    before = income(F(0), alpha, total, borrowed, pts)
    after = income(F(10**8), alpha, total, borrowed, pts)
    assert after < before


@pytest.mark.parametrize("m", MARKETS, ids=lambda m: m.name)
def test_deposit_derivative_uses_lower_utilization_at_every_knot(m):
    pts = breakpoints(m)
    total, alpha, step = F(10**6), F(1, 10), F(1, 10**3)
    for i, (u, _) in enumerate(pts[1:-1]):
        borrowed = total * u / PRECISION
        assert elasticity(u, pts) == segment_elasticity(u, pts, i)
        forward = (
            income(step, alpha, total, borrowed, pts) - income(0, alpha, total, borrowed, pts)
        ) / step
        assert float(income_derivative(alpha, total, borrowed, pts)) == pytest.approx(
            float(forward), rel=1e-6, abs=1e-8
        )

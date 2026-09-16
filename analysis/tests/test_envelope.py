"""Checks on the admissible family and the C^1 branch.

The theme throughout is that the closed forms in the paper are tested against
something that does not assume them: the boundary curves against numerical
quadrature of the integral bound, the elasticity against a central difference of
the rate, and the C^1 claim against one-sided difference quotients rather than
against the formula that was used to build the curve.
"""

from __future__ import annotations

import math

import pytest
from supplier_monotonicity.envelope import (
    SmoothBranch,
    adjacent_rate_cap,
    envelope_from_share,
    fixed_share_cap,
    fixed_share_envelope,
    fixed_share_floor,
    fresh_depositor_envelope,
    fresh_depositor_floor,
    fresh_depositor_share,
    inverse_boundary,
    power_boundary,
    rate_bound,
    share_from_envelope,
)
from supplier_monotonicity.proposal import Kink

O, R_O, R_MAX = 0.80, 0.05, 1.00
UTILIZATIONS = [0.82, 0.85, 0.90, 0.95, 0.98, 0.999]


# -- profiles and the envelope ---------------------------------------------


@pytest.mark.parametrize("alpha", [0.01, 0.05, 0.10, 0.25, 0.50, 1.0])
def test_envelope_and_share_are_inverse(alpha):
    assert share_from_envelope(envelope_from_share(alpha)) == pytest.approx(alpha)


def test_full_pool_share_allows_no_elasticity():
    assert envelope_from_share(1.0) == 0.0


@pytest.mark.parametrize("alpha", [0.0, -0.1, 1.5])
def test_envelope_rejects_shares_outside_the_unit_interval(alpha):
    with pytest.raises(ValueError):
        envelope_from_share(alpha)


@pytest.mark.parametrize("u", [0.05, 0.3, 0.5, 0.9, 0.99])
def test_fresh_depositor_profile_is_one_minus_utilization(u):
    """The fresh-depositor rule eta <= U/(1-U) is the profile alpha_bar = 1-U."""
    assert envelope_from_share(fresh_depositor_share(u)) == pytest.approx(u / (1 - u))
    assert fresh_depositor_envelope()(u) == pytest.approx(u / (1 - u))


def test_fresh_depositor_protects_half_at_half_utilization():
    assert fresh_depositor_share(0.5) == pytest.approx(0.5)
    assert fresh_depositor_share(0.99) == pytest.approx(0.01)


# -- the integral bound vs its closed forms --------------------------------


@pytest.mark.parametrize("u", UTILIZATIONS)
@pytest.mark.parametrize("k", [5.0, 19.0, 40.0])
def test_constant_envelope_integrates_to_the_power_law(u, k):
    got = rate_bound(u, O, R_O, fixed_share_envelope(share_from_envelope(k)))
    assert got == pytest.approx(power_boundary(u, O, R_O, k), rel=1e-9)


@pytest.mark.parametrize("u", UTILIZATIONS)
def test_fresh_depositor_envelope_integrates_to_the_inverse_curve(u):
    got = rate_bound(u, O, R_O, fresh_depositor_envelope())
    assert got == pytest.approx(inverse_boundary(u, O, R_O), rel=1e-8)


def test_inverse_boundary_diverges_at_full_utilization():
    """No finite R_max ever meets this boundary, so the guarantee has no
    endpoint obstruction of the kind K* imposes on a flat target."""
    assert inverse_boundary(1.0, O, R_O) == math.inf
    assert inverse_boundary(1 - 1e-9, O, R_O) > 1e6


def test_fresh_depositor_guarantee_forces_a_positive_base_rate():
    """A curve through the origin has eta = 1 near zero, but the envelope
    U/(1-U) is below 1 for every U < 1/2, so the origin is not admissible."""
    assert fresh_depositor_envelope()(0.25) < 1.0
    assert fresh_depositor_envelope()(0.5) == pytest.approx(1.0)
    assert fresh_depositor_envelope()(0.75) > 1.0


# -- the C^1 branch ---------------------------------------------------------

WIDTHS = [0.0, 0.01, 0.05, 0.10, 0.138]
POSITIVE_WIDTHS = [w for w in WIDTHS if w > 0]


@pytest.mark.parametrize("w", WIDTHS)
def test_branch_reaches_max_rate_exactly(w):
    b = SmoothBranch(O, R_O, R_MAX, w)
    assert b.rate(1.0) == pytest.approx(R_MAX, rel=1e-12)


@pytest.mark.parametrize("w", WIDTHS)
def test_branch_passes_through_the_kink(w):
    b = SmoothBranch(O, R_O, R_MAX, w)
    assert b.rate(O) == pytest.approx(R_O, rel=1e-12)


def test_zero_width_recovers_the_power_law_and_k_star():
    b = SmoothBranch(O, R_O, R_MAX, 0.0)
    assert b.eta_max == pytest.approx(b.k_star)
    assert b.k_star == pytest.approx(Kink(O, R_O, R_MAX).k_star)
    for u in UTILIZATIONS:
        assert b.rate(u) == pytest.approx(power_boundary(u, O, R_O, b.k_star), rel=1e-12)


@pytest.mark.parametrize("w", [0.01, 0.05, 0.10, 0.138])
def test_smoothing_costs_elasticity(w):
    """Every positive width pushes the plateau strictly above the endpoint
    bound, so K* is approached but never attained by a C^1 curve."""
    b = SmoothBranch(O, R_O, R_MAX, w)
    assert b.eta_max > b.k_star


def test_elasticity_cost_is_monotone_in_width():
    peaks = [SmoothBranch(O, R_O, R_MAX, w).eta_max for w in (0.0, 0.02, 0.05, 0.10, 0.15)]
    assert peaks == sorted(peaks)
    assert all(a < b for a, b in zip(peaks, peaks[1:]))


@pytest.mark.parametrize("w", POSITIVE_WIDTHS)
def test_rate_is_c1_at_the_kink(w):
    """One-sided difference quotients of the rate agree at O.

    The C^0 construction fails this: its power branch leaves the kink at K times
    the ramp's slope, which `test_power_branch_is_not_c1` pins.
    """
    b = SmoothBranch(O, R_O, R_MAX, w)
    h = 1e-6
    left = (b.rate(O) - b.rate(O - h)) / h
    right = (b.rate(O + h) - b.rate(O)) / h
    assert left == pytest.approx(right, rel=1e-4)


def test_power_branch_is_not_c1():
    k = 19.0
    ramp_slope = R_O / O
    power_slope = k * R_O / O
    assert power_slope == pytest.approx(k * ramp_slope)
    assert not math.isclose(ramp_slope, power_slope)


@pytest.mark.parametrize("w", [0.01, 0.05, 0.10])
@pytest.mark.parametrize("u", [0.805, 0.82, 0.88, 0.95, 0.999])
def test_rate_prime_matches_a_central_difference(w, u):
    b = SmoothBranch(O, R_O, R_MAX, w)
    h = 1e-7
    numeric = (b.rate(u + h) - b.rate(u - h)) / (2 * h)
    assert b.rate_prime(u) == pytest.approx(numeric, rel=1e-6)


@pytest.mark.parametrize("w", [0.01, 0.05, 0.10])
@pytest.mark.parametrize("u", [0.805, 0.82, 0.88, 0.95, 0.999])
def test_elasticity_matches_the_rate_it_generated(w, u):
    """eta recovered from the rate by central difference equals the profile."""
    b = SmoothBranch(O, R_O, R_MAX, w)
    h = 1e-7
    d = (b.rate(u + h) - b.rate(u - h)) / (2 * h)
    assert u * d / b.rate(u) == pytest.approx(b.eta(u), rel=1e-6)


@pytest.mark.parametrize("w", [0.01, 0.05, 0.10, 0.138])
def test_elasticity_never_exceeds_the_plateau(w):
    b = SmoothBranch(O, R_O, R_MAX, w)
    etas = [b.eta(O + i * (1.0 - O) / 2000) for i in range(2001)]
    assert max(etas) <= b.eta_max + 1e-12
    assert min(etas) >= b.eta_0 - 1e-12


@pytest.mark.parametrize("w", [0.01, 0.05, 0.10, 0.138])
def test_branch_is_strictly_increasing(w):
    b = SmoothBranch(O, R_O, R_MAX, w)
    rates = [b.rate(O + i * (1.0 - O) / 1000) for i in range(1001)]
    assert all(a < b_ for a, b_ in zip(rates, rates[1:]))


@pytest.mark.parametrize("k", [15.0, 19.0, 30.0, 60.0])
def test_max_width_saturates_the_ceiling(k):
    b = SmoothBranch(O, R_O, R_MAX, 0.0)
    w = b.max_width(k)
    assert SmoothBranch(O, R_O, R_MAX, w).eta_max == pytest.approx(
        min(k, 2 * b.k_star - b.eta_0), rel=1e-9
    )


def test_max_width_is_zero_at_the_endpoint_bound():
    b = SmoothBranch(O, R_O, R_MAX, 0.0)
    assert b.max_width(b.k_star) == pytest.approx(0.0, abs=1e-12)


def test_max_width_grows_as_the_ceiling_relaxes():
    b = SmoothBranch(O, R_O, R_MAX, 0.0)
    widths = [b.max_width(k) for k in (14.0, 15.0, 19.0, 30.0, 60.0)]
    assert all(a <= b_ for a, b_ in zip(widths, widths[1:]))
    assert widths[-1] == b.log_span


@pytest.mark.parametrize("w", [0.01, 0.05, 0.10, 0.138])
def test_protected_share_is_continuous_across_the_kink(w):
    """The economic point of C^1: alpha_safe slides instead of jumping.

    Under the power branch it drops from 1/2 to 1/(1+K) at a single point.
    """
    b = SmoothBranch(O, R_O, R_MAX, w)
    assert b.protected_share(O) == pytest.approx(0.5)
    assert b.protected_share(O + 1e-9) == pytest.approx(0.5, rel=1e-6)
    assert b.protected_share(1.0) == pytest.approx(b.peak_protected_share)


@pytest.mark.parametrize("w", [-0.1, 0.39, 10.0])
def test_branch_rejects_infeasible_widths(w):
    with pytest.raises(ValueError):
        SmoothBranch(O, R_O, R_MAX, w)


def test_branch_rejects_inverted_endpoints():
    with pytest.raises(ValueError):
        SmoothBranch(O, 1.0, 0.5, 0.05)


def test_zero_width_is_exactly_the_non_c1_case():
    """w = 0 is the power law, and it leaves the kink at eta_max times the ramp
    slope. It is the boundary the C^1 family approaches without reaching."""
    b = SmoothBranch(O, R_O, R_MAX, 0.0)
    h = 1e-8
    left = (b.rate(O) - b.rate(O - h)) / h
    right = (b.rate(O + h) - b.rate(O)) / h
    assert right == pytest.approx(b.eta_max * left, rel=1e-5)
    assert right > left


# -- discretisation of a smooth boundary ------------------------------------


@pytest.mark.parametrize("a,b", [(0.80, 0.90), (0.85, 0.90), (0.90, 0.95), (0.95, 0.98)])
def test_chord_of_the_power_boundary_overshoots_at_its_left_end(a, b):
    """Sampling a convex boundary overshoots the elasticity it was drawn from.

    The chord's slope is the average of the slopes it spans, so it is steeper
    than the curve at the LEFT endpoint and shallower at the right one. The
    chord also has negative intercept, so eta decreases across the segment and
    the left end is where it binds. Both halves are pinned here because the
    direction is easy to state backwards.
    """
    k = 19.0
    rate = lambda u: power_boundary(u, O, R_O, k)
    slope_at = lambda u: k * rate(u) / u
    m = (rate(b) - rate(a)) / (b - a)

    assert m > slope_at(a), "chord must be steeper than the curve at the left end"
    assert m < slope_at(b), "and shallower than it at the right end"

    assert rate(a) - m * a < 0, "chord intercept is negative, so eta decreases"
    eta_left, eta_right = a * m / rate(a), b * m / rate(b)
    assert eta_left > eta_right

    assert eta_left > k, "the sampled segment overshoots the target elasticity"
    assert eta_right < k, "at the right end it undershoots it"


# -- the compliant floor for a piecewise curve ------------------------------

KNOTS = [0.00, 0.80, 0.90, 0.95, 0.98, 0.995, 0.9999]
TABLE1 = [0.05, 0.09, 0.135, 0.20, 0.32, 0.56, 1.10]


def test_floor_reaches_the_top_rate_and_satisfies_every_segment():
    floor = fresh_depositor_floor(KNOTS, 1.10)
    assert floor[-1] == pytest.approx(1.10)
    for i in range(len(KNOTS) - 1):
        cap = adjacent_rate_cap(KNOTS[i], KNOTS[i + 1])
        assert floor[i + 1] / floor[i] == pytest.approx(cap)


def test_table1_is_the_cheapest_compliant_curve_through_its_knots():
    """Table 1 sits on the floor, so it is a lower bound rather than a soft choice."""
    floor = fresh_depositor_floor(KNOTS, TABLE1[-1])
    for got, low in zip(TABLE1, floor):
        assert got >= low - 1e-12
        assert got == pytest.approx(low, rel=0.03)


def test_a_flat_then_jump_curve_sits_below_the_floor_where_it_violates():
    """Compliance forces the middle of the curve UP, not down."""
    violating = [0.05, 0.06, 0.07, 0.20, 0.45, 0.70, 1.10]
    floor = fresh_depositor_floor(KNOTS, violating[-1])
    under = [i for i, (v, f) in enumerate(zip(violating, floor)) if v < f - 1e-9]
    assert under, "this curve should dip below the floor somewhere"
    worst = max(under)
    assert violating[worst + 1] / violating[worst] > adjacent_rate_cap(
        KNOTS[worst], KNOTS[worst + 1]
    ), "and violate the rule just above it"


@pytest.mark.parametrize("top", [0.5, 1.10, 3.0])
def test_floor_scales_linearly_with_the_top_rate(top):
    base = fresh_depositor_floor(KNOTS, 1.0)
    scaled = fresh_depositor_floor(KNOTS, top)
    for b, sc in zip(base, scaled):
        assert sc == pytest.approx(b * top)


# -- the same construction against the fixed-share rule ---------------------


def test_fixed_share_floor_reaches_the_top_and_respects_the_ceiling():
    k = 19.0
    floor = fixed_share_floor(KNOTS, 1.10, k, base_rate=0.05)
    assert floor[-1] == pytest.approx(1.10)
    for i in range(1, len(KNOTS) - 1):
        cap = fixed_share_cap(KNOTS[i], KNOTS[i + 1], k)
        assert floor[i + 1] / floor[i] <= cap + 1e-9


def test_first_segment_is_unconstrained_under_the_fixed_share_rule():
    """Starting at zero utilization the ceiling cannot bind, which is why this
    rule tolerates a curve through the origin and the fresh-depositor one does not."""
    assert math.isinf(fixed_share_cap(0.0, 0.80, 19.0))
    assert adjacent_rate_cap(0.0, 0.80) == pytest.approx(1.8)


def test_the_two_rules_are_not_nested_on_a_piecewise_curve():
    """Neither floor dominates: they cross, exactly as the envelopes do."""
    k = 19.0
    fs = fixed_share_floor(KNOTS, 1.10, k, base_rate=0.05)
    fd = fresh_depositor_floor(KNOTS, 1.10)
    assert any(a > b for a, b in zip(fs, fd)), "fixed share demands more somewhere"
    assert any(a < b for a, b in zip(fs, fd)), "and less somewhere else"


@pytest.mark.parametrize("k", [9.0, 19.0, 99.0])
def test_a_looser_ceiling_lowers_the_fixed_share_floor(k):
    loose = fixed_share_floor(KNOTS, 1.10, k * 2, base_rate=0.05)
    tight = fixed_share_floor(KNOTS, 1.10, k, base_rate=0.05)
    assert all(a <= b + 1e-12 for a, b in zip(loose, tight))


@pytest.mark.parametrize("k", [19.0, 30.0, 60.0, 1e6])
def test_max_width_preserves_endpoint_and_stays_inside_branch(k):
    reference = SmoothBranch(O, R_O, R_MAX, 0.0)
    branch = SmoothBranch(O, R_O, R_MAX, reference.max_width(k))
    assert branch.width <= branch.log_span
    assert branch.rate(1.0) == pytest.approx(R_MAX, rel=1e-12)
    assert branch.eta_max <= k + 1e-12

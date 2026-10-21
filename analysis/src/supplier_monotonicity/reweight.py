"""Deriving segment weights from a target elasticity.

Holding elasticity at a constant `K` means `U * R' / R = K`, whose solution is
the power curve `R(U) = R_o * (U / O) ** K`. Onchain models evaluate linear segments
rather than fractional powers, so the curve is sampled at the existing
breakpoints and the samples are converted back into the weight table's format.

Sampling introduces its own error in one direction only, though not for the
reason it first looks like. A chord's slope is the average of the slopes it
spans, so on a convex curve it is *less* steep than the curve at the segment's
right end and *more* steep at its left end. The chord also has negative
intercept, so `eta` decreases across the segment and the left end is where it
binds. The discretised elasticity therefore overshoots `K`, and it overshoots
there: sampling `R_o*(U/O)**19` at 80% and 90% gives a segment whose elasticity
at 80% is about 67. Any target has to be chosen with real headroom.
"""

from __future__ import annotations

from fractions import Fraction as F

from .curve import PRECISION, SEGMENTS, WEIGHTS_DIVISOR, Market, breakpoints
from .elasticity import max_elasticity, minimum_feasible_elasticity


def constant_elasticity_weights(m: Market, k: float | None = None) -> list[tuple[int, int]]:
    """Weight table tracking `R_o * (U / O) ** k`, defaulting to `k = K*`.

    `K*` is the smallest elasticity that still reaches `max_borrow_rate` at full
    utilization, so it is the least aggressive curve the endpoints permit.
    """
    k = minimum_feasible_elasticity(m) if k is None else k
    extra = m.max_borrow_rate - m.optimal_borrow_rate
    weights: list[int] = []
    prev = float(m.optimal_borrow_rate)
    for bp, _ in SEGMENTS:
        target = m.optimal_borrow_rate * (bp / m.optimal_utilization) ** k
        target = min(target, float(m.max_borrow_rate))
        weights.append(round((target - prev) / extra * WEIGHTS_DIVISOR))
        prev = target
    weights[-1] += WEIGHTS_DIVISOR - sum(weights)
    return [(bp, w) for (bp, _), w in zip(SEGMENTS, weights)]


def summarise(m: Market, segments: list[tuple[int, int]] | None = None) -> dict:
    """Worst-case elasticity and protected share for a market and weight table."""
    pts = breakpoints(m, segments)
    eta, where = max_elasticity(pts)
    return {
        "market": m.name,
        "max_eta": float(eta),
        "at_utilization": float(where) / PRECISION,
        "alpha_safe": float(F(1) / (1 + eta)),
        "k_star": minimum_feasible_elasticity(m),
        "alpha_max": 1.0 / (1.0 + minimum_feasible_elasticity(m)),
    }

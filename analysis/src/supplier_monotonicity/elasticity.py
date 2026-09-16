"""Borrow-rate elasticity and the deposit-monotonicity constraint.

For a supplier holding share `alpha` of a market's deposits, adding to the
position changes annualized income by

    dI/d_delta = U * R_b(U) * [1 - alpha * (1 + eta(U))]

where `eta(U) = U * R_b'(U) / R_b(U)` is the elasticity of the borrow rate with
respect to utilization. Income therefore stops rising once
`alpha > 1 / (1 + eta)`, and depositing more earns less.
"""

from __future__ import annotations

import math
from fractions import Fraction as F

from .curve import PRECISION, Market, borrow_rate


def segment_elasticity(u: F, pts: list[tuple[F, F]], i: int) -> F:
    """`eta` at `u` using segment `i`'s slope.

    The segment must be given explicitly. Rate is continuous at a breakpoint but
    slope is not, so `eta` there is one-sided and resolving the breakpoint to a
    segment implicitly picks the wrong side half the time.
    """
    (u0, r0), (u1, r1) = pts[i], pts[i + 1]
    if u1 == u0:
        return F(0)
    slope = (r1 - r0) / (u1 - u0)
    rate = r0 + slope * (F(u) - u0)
    return F(0) if rate == 0 else F(u) * slope / rate


def elasticity(u: F | int, pts: list[tuple[F, F]]) -> F:
    """Left-hand `eta` at `u`: a deposit enters from lower utilization."""
    uu = F(u)
    for i in range(len(pts) - 1):
        if pts[i][0] <= uu <= pts[i + 1][0]:
            return segment_elasticity(uu, pts, i)
    return segment_elasticity(uu, pts, len(pts) - 2)


def max_elasticity(pts: list[tuple[F, F]]) -> tuple[F, F]:
    """Largest `eta` on the curve, and where it occurs.

    `eta` is monotone across a linear segment, so both endpoints of every
    segment bound it and no interior search is needed.
    """
    best, where = F(0), F(0)
    for i in range(len(pts) - 1):
        (u0, _), (u1, _) = pts[i], pts[i + 1]
        if u1 == u0:
            continue
        for u in (u0, u1):
            if u == 0:
                continue
            e = segment_elasticity(u, pts, i)
            if e > best:
                best, where = e, u
    return best, where


def alpha_safe(eta: F) -> F:
    """Largest deposit share that is protected at this elasticity."""
    return F(1) / (1 + eta)


def max_elasticity_allowed(alpha_bar: float) -> float:
    """`K = (1 - alpha) / alpha`, the elasticity ceiling a protection target implies."""
    return (1.0 - alpha_bar) / alpha_bar


def minimum_feasible_elasticity(m: Market) -> float:
    """`K* = ln(R_max / R_o) / ln(1 / O)`.

    The endpoints alone force this much elasticity somewhere on the curve, so no
    IRM with these endpoints can protect more than `1 / (1 + K*)` of the market.
    """
    return math.log(m.max_borrow_rate / m.optimal_borrow_rate) / math.log(
        PRECISION / m.optimal_utilization
    )


def violations(pts: list[tuple[F, F]], k: int) -> list[tuple[F, F, F]]:
    """Segments whose elasticity exceeds `k`, as `(u_start, u_end, max_eta)`.

    Uses the same division-free test the onchain validation would run:
    `U * dr <= K * r * dU` at both endpoints of each segment.
    """
    out = []
    for i in range(len(pts) - 1):
        (u0, r0), (u1, r1) = pts[i], pts[i + 1]
        if u1 == u0 or r1 == r0:
            continue
        du, dr = u1 - u0, r1 - r0
        if u0 * dr > k * r0 * du or u1 * dr > k * r1 * du:
            out.append(
                (u0, u1, max(segment_elasticity(u0, pts, i), segment_elasticity(u1, pts, i)))
            )
    return out


def income_derivative(alpha: F, total: F, borrowed: F, pts: list[tuple[F, F]]) -> F:
    """`dI/d_delta` from the product and chain rules directly.

    Deliberately does not use the `1 - alpha * (1 + eta)` identity, so comparing
    the two is a real check of the rearrangement rather than a restatement of it.
    Working in real units, `dR/dU` equals the segment slope in precision units,
    because the two precision factors cancel.
    """
    u_prec = borrowed * PRECISION / total
    i = _segment_index_for(u_prec, pts)
    (u0, r0), (u1, r1) = pts[i], pts[i + 1]
    slope = F(0) if u1 == u0 else (r1 - r0) / (u1 - u0)

    u = u_prec / PRECISION
    rate = borrow_rate(u_prec, pts) / PRECISION
    b = alpha * total
    du_ddelta = -u / total
    return u * rate + b * (rate + u * slope) * du_ddelta


def _segment_index_for(u: F, pts: list[tuple[F, F]]) -> int:
    for i in range(len(pts) - 1):
        if pts[i][0] <= u <= pts[i + 1][0]:
            return i
    return len(pts) - 2


def income(delta: F, alpha: F, total: F, borrowed: F, pts: list[tuple[F, F]]) -> F:
    """Annualized interest income of a supplier who adds `delta`, with `B` fixed."""
    t = total + delta
    b = alpha * total + delta
    u = min(borrowed * PRECISION / t, F(PRECISION))
    return b * (u / PRECISION) * (borrow_rate(u, pts) / PRECISION)

"""The illustrative spot interest rate model, as an exact integer port and as an
exact rational model.

The integer port mirrors a fixed-point `calculate_borrow_rate` routine line for
line, including the flooring divisions and the trailing
`max(rate, min_borrow_rate)`. The rational
model represents the same curve as a list of breakpoints with `Fraction`
coordinates, which is what the elasticity analysis runs on.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F

#: Utilization and rate share a single fixed-point precision.
PRECISION = 1_000_000

#: Segment breakpoints and weights of the illustrative model.
SEGMENTS: list[tuple[int, int]] = [
    (850_000, 50),
    (900_000, 100),
    (950_000, 150),
    (990_000, 200),
    (995_000, 250),
    (1_000_000, 250),
]

WEIGHTS_DIVISOR = 1000


def min_borrow_rate(min_borrow_rate_u8: int) -> int:
    """The minimum borrow rate: the u8 field is in 0.5% steps."""
    return min_borrow_rate_u8 * (PRECISION // 200)


@dataclass(frozen=True)
class Market:
    """The three tunables an admin sets, plus the rate floor."""

    name: str
    optimal_utilization: int
    optimal_borrow_rate: int
    max_borrow_rate: int
    min_borrow_rate: int = 0

    @property
    def floor(self) -> int:
        return min_borrow_rate(self.min_borrow_rate)


def borrow_rate_int(utilization: int, m: Market) -> int:
    """Integer-identical to the onchain `calculate_borrow_rate`."""
    optimal_util = m.optimal_utilization
    optimal_rate = m.optimal_borrow_rate

    if utilization <= optimal_util:
        slope = optimal_rate * PRECISION // optimal_util
        rate = utilization * slope // PRECISION
    else:
        total_extra_rate = m.max_borrow_rate - optimal_rate
        rate = optimal_rate
        prev_util = optimal_util
        for bp, weight in SEGMENTS:
            if bp <= prev_util:
                continue
            segment_rate_total = total_extra_rate * weight // WEIGHTS_DIVISOR
            if utilization <= bp:
                rate += segment_rate_total * (utilization - prev_util) // (bp - prev_util)
                break
            rate += segment_rate_total
            prev_util = bp

    return max(rate, m.floor)


def breakpoints(m: Market, segments: list[tuple[int, int]] | None = None) -> list[tuple[F, F]]:
    """The same curve as exact `(utilization, borrow_rate)` breakpoints.

    Built unfloored, then the `max(rate, floor)` clamp is applied by inserting
    the crossing point. That keeps the floored region a segment of its own, so
    its zero slope (and therefore zero elasticity) is represented exactly
    rather than smeared into the ramp above it.
    """
    segments = SEGMENTS if segments is None else segments
    raw: list[tuple[F, F]] = [(F(0), F(0)), (F(m.optimal_utilization), F(m.optimal_borrow_rate))]
    rate = m.optimal_borrow_rate
    prev_util = m.optimal_utilization
    extra = m.max_borrow_rate - m.optimal_borrow_rate
    for bp, weight in segments:
        if bp <= prev_util:
            continue
        rate += extra * weight // WEIGHTS_DIVISOR
        raw.append((F(bp), F(rate)))
        prev_util = bp

    floor = F(m.floor)
    if floor <= 0:
        return raw

    out: list[tuple[F, F]] = []
    for i, (u, r) in enumerate(raw):
        if i > 0:
            (u0, r0), (u1, r1) = raw[i - 1], raw[i]
            if (r0 < floor) != (r1 < floor) and r1 != r0:
                crossing = u0 + (u1 - u0) * (floor - r0) / (r1 - r0)
                out.append((crossing, floor))
        out.append((u, max(r, floor)))
    return out


def borrow_rate(utilization: F | int, pts: list[tuple[F, F]]) -> F:
    """Exact borrow rate from the rational model."""
    u = F(utilization)
    i = _segment_index(u, pts)
    (u0, r0), (u1, r1) = pts[i], pts[i + 1]
    return r0 + (r1 - r0) * (u - u0) / (u1 - u0)


def supply_rate(utilization: F | int, pts: list[tuple[F, F]]) -> F:
    """`R_s = U * R_b`, matching how accumulated interest is scaled."""
    u = F(utilization)
    return (u / PRECISION) * (borrow_rate(u, pts) / PRECISION)


def _segment_index(u: F, pts: list[tuple[F, F]]) -> int:
    for i in range(len(pts) - 1):
        if pts[i][0] <= u <= pts[i + 1][0]:
            return i
    return len(pts) - 2

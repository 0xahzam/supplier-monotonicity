"""The single-kink model and the elasticity-capped curve proposed against it.

The article works against the standard hockey stick

    R_old(U) = R_o · U/O                 U <= O
             = R_o + m·(U - O)           U > O,     m = (R_max - R_o)/(1 - O)

Holding elasticity at a constant K solves to the power curve R_o·(U/O)^K, which
is the steepest curve still satisfying the constraint. The proposal follows the
old curve to the kink, switches to the power branch while the old branch is too
elastic, and returns to the old branch at the first point where the two meet:

    R_new(U) = R_o · U/O                 U <= O
             = R_o · (U/O)^K             O < U < U_c
             = R_o + m·(U - O)           U_c <= U <= 1

Everything here is in real units, so a rate of 0.9 is 90% and a utilization of
0.8 is 80%. Fractional powers keep this module on floats, unlike `curve.py`.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass(frozen=True)
class Kink:
    """A single-kink rate curve."""

    optimal_utilization: float
    optimal_rate: float
    max_rate: float

    @property
    def slope(self) -> float:
        """`m`, the post-kink slope."""
        return (self.max_rate - self.optimal_rate) / (1.0 - self.optimal_utilization)

    @property
    def k_star(self) -> float:
        """`K* = ln(R_max/R_o) / ln(1/O)`, the elasticity the endpoints already force."""
        return math.log(self.max_rate / self.optimal_rate) / math.log(
            1.0 / self.optimal_utilization
        )

    @property
    def alpha_max(self) -> float:
        """Largest share any curve with these endpoints could protect."""
        return 1.0 / (1.0 + self.k_star)

    @property
    def peak_elasticity(self) -> float:
        """`O·m/R_o`, reached immediately above the kink.

        The post-kink branch has intercept `R_o - m·O`, which is negative for any
        real hockey stick, so its elasticity falls across the branch and the kink
        is the worst point on the whole curve.
        """
        return self.optimal_utilization * self.slope / self.optimal_rate


def old_rate(u: float, c: Kink) -> float:
    if u <= c.optimal_utilization:
        return c.optimal_rate * u / c.optimal_utilization
    return c.optimal_rate + c.slope * (u - c.optimal_utilization)


def power_rate(u: float, c: Kink, k: float) -> float:
    """`R_o·(U/O)^K`, the constant-elasticity branch anchored at the kink."""
    return c.optimal_rate * (u / c.optimal_utilization) ** k


def rejoin(c: Kink, k: float, tol: float = 1e-12) -> float:
    """`U_c`, the first utilization above the kink where the branches meet again.

    Returns the kink itself when the old curve already satisfies the constraint,
    in which case nothing is replaced.
    """
    o = c.optimal_utilization
    if k >= c.peak_elasticity:
        return o
    lo, hi = o, 1.0
    if power_rate(hi, c, k) < old_rate(hi, c):
        return 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if power_rate(mid, c, k) < old_rate(mid, c):
            lo = mid
        else:
            hi = mid
        if hi - lo < tol:
            break
    return (lo + hi) / 2


def new_rate(u: float, c: Kink, k: float, u_c: float | None = None) -> float:
    u_c = rejoin(c, k) if u_c is None else u_c
    if u <= c.optimal_utilization:
        return c.optimal_rate * u / c.optimal_utilization
    if u < u_c:
        return power_rate(u, c, k)
    return old_rate(u, c)


def elasticity_of(u: float, rate_fn, h: float = 1e-7) -> float:
    """`η = U·R'(U)/R(U)` by central difference, for plotting either curve."""
    r = rate_fn(u)
    if r <= 0:
        return 0.0
    d = (rate_fn(u + h) - rate_fn(u - h)) / (2 * h)
    return u * d / r


def feasible(c: Kink, k: float) -> bool:
    """Whether the constrained branch can still reach `R_max` by full utilization."""
    return k >= c.k_star


def income(delta: float, alpha: float, total: float, borrowed: float, rate_fn) -> float:
    """Annual interest income of a supplier who adds `delta`, with borrowings fixed."""
    t = total + delta
    b = alpha * total + delta
    u = min(borrowed / t, 1.0)
    return b * u * rate_fn(u)

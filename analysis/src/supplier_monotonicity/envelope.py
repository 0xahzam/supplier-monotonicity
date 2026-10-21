"""The admissible family of borrow-rate curves, and smooth members of it.

The monotonicity condition `alpha * (1 + eta) <= 1` constrains the supplier, not
the curve. A protocol turns it into a curve constraint by choosing a *protection
profile* `alpha_bar(U)`: the largest supplier share it intends to protect at
utilization `U`. That profile fixes an elasticity envelope

    E(U) = (1 - alpha_bar(U)) / alpha_bar(U)

and the design constraint becomes `eta(U) <= E(U)`. Since
`eta = U * R'(U) / R(U) = d ln R / d ln U`, the constraint is a differential
inequality whose integrated form bounds the whole curve,

    R(U_b) <= R(U_a) * exp( integral from U_a to U_b of E(v)/v dv ).

Equality gives the boundary curve for that profile. Two profiles matter here:

    alpha_bar(U) = const        -> E = K        -> R = R_a * (U/U_a)^K
    alpha_bar(U) = 1 - U        -> E = U/(1-U)  -> R = R_a * (1-U_a)/(1-U)

The second is the fresh-depositor guarantee, restated as a profile. Its boundary
diverges at full utilization, which is why it never collides with a finite
`R_max` the way the constant-elasticity ceiling does.

The same integral, read forwards rather than as a bound, constructs curves:
prescribing a continuous `eta(U)` and setting
`R(U) = R_a * exp(integral of eta(v)/v dv)` yields `R' = eta * R / U`, which is
continuous whenever `eta` is. That is the route to a `C^1` curve, and it is what
`SmoothBranch` does.
"""

from __future__ import annotations

import math
from collections.abc import Callable
from dataclasses import dataclass

__all__ = [
    "adjacent_rate_cap",
    "fresh_depositor_floor",
    "fixed_share_cap",
    "fixed_share_floor",
    "envelope_from_share",
    "share_from_envelope",
    "fixed_share_envelope",
    "fresh_depositor_envelope",
    "fresh_depositor_share",
    "rate_bound",
    "power_boundary",
    "inverse_boundary",
    "SmoothBranch",
]


# --------------------------------------------------------------------------
# Protection profiles and the envelope they imply
# --------------------------------------------------------------------------


def envelope_from_share(alpha_bar: float) -> float:
    """`E = (1 - alpha_bar) / alpha_bar`, the elasticity a protection target allows."""
    if not 0.0 < alpha_bar <= 1.0:
        raise ValueError("alpha_bar must lie in (0, 1]")
    return (1.0 - alpha_bar) / alpha_bar


def share_from_envelope(e: float) -> float:
    """`alpha_bar = 1 / (1 + E)`, the inverse of `envelope_from_share`."""
    return 1.0 / (1.0 + e)


def fixed_share_envelope(alpha_bar: float) -> Callable[[float], float]:
    """Constant envelope `E(U) = K` from a flat protection target."""
    k = envelope_from_share(alpha_bar)
    return lambda _u: k


def fresh_depositor_share(u: float) -> float:
    """`alpha_bar(U) = 1 - U`.

    A fresh depositor entering from `u_0` ends at share `1 - u/u_0`; the worst
    case over all feasible starts is `u_0 = 1`, so protecting every fresh
    depositor is exactly the profile `1 - U`. It protects half the pool at 50%
    utilization and only 1% of it at 99%, which is why it tolerates a steep
    emergency branch that a flat target would reject.
    """
    return 1.0 - u


def fresh_depositor_envelope() -> Callable[[float], float]:
    """`E(U) = U / (1 - U)`, the envelope of the fresh-depositor guarantee."""
    return lambda u: math.inf if u >= 1.0 else u / (1.0 - u)


# --------------------------------------------------------------------------
# The integral bound
# --------------------------------------------------------------------------


def rate_bound(
    u: float,
    u_a: float,
    r_a: float,
    e_fn: Callable[[float], float],
    steps: int = 20_000,
) -> float:
    """`R_a * exp(integral from u_a to u of E(v)/v dv)`, by Simpson's rule.

    The largest rate at `u` reachable from `(u_a, r_a)` without ever exceeding
    the envelope. Closed forms exist for both profiles used in the paper
    (`power_boundary`, `inverse_boundary`); this is the general case, used for
    arbitrary envelopes and as an independent check on those closed forms.
    """
    if u == u_a:
        return r_a
    if steps % 2:
        steps += 1
    h = (u - u_a) / steps
    total = 0.0
    for i in range(steps + 1):
        v = u_a + i * h
        w = 1 if i in (0, steps) else (4 if i % 2 else 2)
        total += w * e_fn(v) / v
    return r_a * math.exp(total * h / 3.0)


def power_boundary(u: float, u_a: float, r_a: float, k: float) -> float:
    """`R_a * (U/U_a)^K`, the constant-elasticity boundary."""
    return r_a * (u / u_a) ** k


def inverse_boundary(u: float, u_a: float, r_a: float) -> float:
    """`R_a * (1 - U_a) / (1 - U)`, the fresh-depositor boundary."""
    if u >= 1.0:
        return math.inf
    return r_a * (1.0 - u_a) / (1.0 - u)


# --------------------------------------------------------------------------
# A C^1 branch built from a prescribed elasticity profile
# --------------------------------------------------------------------------


def _smoothstep(t: float) -> float:
    """`3t^2 - 2t^3` on [0, 1], with zero derivative at both ends."""
    if t <= 0.0:
        return 0.0
    if t >= 1.0:
        return 1.0
    return t * t * (3.0 - 2.0 * t)


def _smoothstep_integral(t: float) -> float:
    """`integral from 0 to t of _smoothstep`, i.e. `t^3 - t^4/2`; equals 1/2 at t = 1."""
    if t <= 0.0:
        return 0.0
    if t >= 1.0:
        return 0.5 + (t - 1.0)
    return t**3 - t**4 / 2.0


@dataclass(frozen=True)
class SmoothBranch:
    """A `C^1` replacement for the post-kink branch, at fixed endpoints.

    The elasticity is prescribed in log-utilization `x = ln(U/O)`, rising from
    `eta_0` to a plateau `eta_max` over a width `width`, then held:

        eta(x) = eta_0 + (eta_max - eta_0) * smoothstep(x / width)   x <= width
               = eta_max                                            x >  width

    `eta_0` is the elasticity of the branch below the kink, so matching it makes
    the rate curve `C^1` at the kink; the smoothstep's vanishing endpoint slope
    makes `eta` itself `C^1`, hence the rate `C^2` there. The rate follows from
    the integral construction, so it is `C^1` wherever `eta` is continuous.

    `eta_max` is not free: the branch must still reach `R_max` at `U = 1`, which
    pins `integral of eta dx = ln(R_max/R_o)` and leaves

        eta_max = (A - eta_0 * w / 2) / (L - w / 2)

    with `A = ln(R_max/R_o)` and `L = ln(1/O)`. At `w = 0` this is `K* = A/L`,
    the endpoint bound. For every `w > 0` it is strictly larger whenever
    `K* > eta_0`, so smoothness has a price and `K*` is unattainable under `C^1`.
    """

    optimal_utilization: float
    optimal_rate: float
    max_rate: float
    width: float
    eta_0: float = 1.0

    def __post_init__(self) -> None:
        if not 0.0 < self.optimal_utilization < 1.0:
            raise ValueError("optimal_utilization must lie in (0, 1)")
        if self.optimal_rate <= 0.0 or self.max_rate <= self.optimal_rate:
            raise ValueError("require 0 < optimal_rate < max_rate")
        if not 0.0 <= self.width <= self.log_span:
            raise ValueError("width must lie in [0, ln(1/O)]")

    # -- fixed quantities -------------------------------------------------

    @property
    def log_span(self) -> float:
        """`L = ln(1/O)`, the length of the branch in log-utilization."""
        return math.log(1.0 / self.optimal_utilization)

    @property
    def log_rise(self) -> float:
        """`A = ln(R_max/R_o)`, the rate the branch must cover."""
        return math.log(self.max_rate / self.optimal_rate)

    @property
    def k_star(self) -> float:
        """`K* = A / L`, the elasticity the endpoints alone force."""
        return self.log_rise / self.log_span

    @property
    def eta_max(self) -> float:
        """Plateau elasticity implied by the endpoints and the smoothing width."""
        w = self.width
        return (self.log_rise - self.eta_0 * w / 2.0) / (self.log_span - w / 2.0)

    @property
    def peak_protected_share(self) -> float:
        """`1 / (1 + eta_max)`, the share protected across the plateau."""
        return 1.0 / (1.0 + self.eta_max)

    def max_width(self, k: float) -> float:
        """Largest smoothing width whose plateau still satisfies `eta <= k`.

        `w <= 2 L (k - K*) / (k - eta_0)`. It is zero at `k = K*` and grows
        up to `L`, where the ramp fills the entire branch. Widths beyond
        `L` are outside this construction.
        """
        if k <= self.eta_0:
            raise ValueError("k must exceed eta_0")
        if k < self.k_star:
            return 0.0
        return min(self.log_span, 2.0 * self.log_span * (k - self.k_star) / (k - self.eta_0))

    # -- the curve --------------------------------------------------------

    def eta(self, u: float) -> float:
        """`eta(U)` on the branch; `eta_0` at or below the kink."""
        if u <= self.optimal_utilization:
            return self.eta_0
        x = math.log(u / self.optimal_utilization)
        if self.width <= 0.0:
            return self.eta_max
        return self.eta_0 + (self.eta_max - self.eta_0) * _smoothstep(x / self.width)

    def _log_rise_to(self, x: float) -> float:
        """`integral from 0 to x of eta`, in closed form for this profile."""
        w, e0, em = self.width, self.eta_0, self.eta_max
        if w <= 0.0:
            return em * x
        if x <= w:
            return e0 * x + (em - e0) * w * _smoothstep_integral(x / w)
        return w * (e0 + em) / 2.0 + em * (x - w)

    def rate(self, u: float) -> float:
        """`R(U)`: the linear ramp below the kink, the smooth branch above it."""
        o, r_o = self.optimal_utilization, self.optimal_rate
        if u <= o:
            return r_o * (u / o) ** self.eta_0
        return r_o * math.exp(self._log_rise_to(math.log(u / o)))

    def rate_prime(self, u: float) -> float:
        """`R'(U) = eta(U) R(U) / U`, continuous because `eta` is."""
        return self.eta(u) * self.rate(u) / u

    def protected_share(self, u: float) -> float:
        """`alpha_safe(U) = 1 / (1 + eta(U))` along the branch."""
        return 1.0 / (1.0 + self.eta(u))


# --------------------------------------------------------------------------
# Piecewise curves: what the adjacent rate rule actually pins down
# --------------------------------------------------------------------------


def adjacent_rate_cap(u_lo: float, u_hi: float) -> float:
    """`1 + (u_hi - u_lo)/(1 - u_lo)`, the largest admissible ratio `R_hi/R_lo`."""
    return 1.0 + (u_hi - u_lo) / (1.0 - u_lo)


def fresh_depositor_floor(knots: list[float], top_rate: float) -> list[float]:
    """Smallest rates at each knot that satisfy the rule and still reach `top_rate`.

    The adjacent rate rule caps `R_{i+1}/R_i`, so fixing the rate at the final
    knot forces a lower bound on every knot beneath it: divide back down by each
    segment's cap. Any compliant curve through these knots reaching `top_rate`
    lies at or above the result.

    This is what makes a compliant curve expensive rather than cheap. A curve
    that stays flat through the middle and jumps at the end sits *below* this
    floor in the middle, and that is precisely why it violates the rule.
    """
    if len(knots) < 2:
        raise ValueError("need at least two knots")
    out = [0.0] * len(knots)
    out[-1] = top_rate
    for i in range(len(knots) - 2, -1, -1):
        out[i] = out[i + 1] / adjacent_rate_cap(knots[i], knots[i + 1])
    return out


def fixed_share_cap(u_lo: float, u_hi: float, k: float) -> float:
    """Largest admissible `R_hi/R_lo` under the fixed-share ceiling `eta <= k`.

    Elasticity is monotone across a linear segment, so the division-free test
    `U dr <= k r dU` binds at one end or the other. The left end gives
    `1 + k dU/u_lo`; the right end gives `u_hi/(u_hi - k dU)`, which is vacuous
    once `k dU >= u_hi` because the segment can then be arbitrarily steep
    without the right endpoint's elasticity exceeding `k`.
    """
    du = u_hi - u_lo
    left = math.inf if u_lo <= 0 else 1.0 + k * du / u_lo
    den = u_hi - k * du
    right = math.inf if den <= 0 else u_hi / den
    return min(left, right)


def fixed_share_floor(
    knots: list[float], top_rate: float, k: float, base_rate: float = 0.0
) -> list[float]:
    """Smallest rates at each knot satisfying `eta <= k` and reaching `top_rate`.

    The same construction as `fresh_depositor_floor` against the other rule.
    Where a segment's cap is unbounded the floor is not pinned, and `base_rate`
    is used instead; that happens on the first segment, which starts at zero
    utilization and is the reason this rule, unlike the fresh-depositor one,
    permits a curve through the origin.
    """
    if len(knots) < 2:
        raise ValueError("need at least two knots")
    out = [0.0] * len(knots)
    out[-1] = top_rate
    for i in range(len(knots) - 2, -1, -1):
        cap = fixed_share_cap(knots[i], knots[i + 1], k)
        out[i] = base_rate if math.isinf(cap) else out[i + 1] / cap
    return out

"""Deposit monotonicity for utilization-based interest rate models.

Measures the elasticity of the illustrative spot borrow rate curve and reports the
largest supplier share the curve protects from earning less by depositing more.
"""

from .curve import (
    PRECISION,
    SEGMENTS,
    Market,
    borrow_rate,
    borrow_rate_int,
    breakpoints,
    supply_rate,
)
from .elasticity import (
    alpha_safe,
    elasticity,
    income,
    income_derivative,
    max_elasticity,
    max_elasticity_allowed,
    minimum_feasible_elasticity,
    violations,
)
from .markets import load as load_markets

__all__ = [
    "PRECISION",
    "SEGMENTS",
    "Market",
    "borrow_rate",
    "borrow_rate_int",
    "breakpoints",
    "supply_rate",
    "alpha_safe",
    "elasticity",
    "income",
    "income_derivative",
    "max_elasticity",
    "max_elasticity_allowed",
    "minimum_feasible_elasticity",
    "violations",
    "load_markets",
]

"""Frozen illustrative market configurations, in units of 1e6."""

from __future__ import annotations

import json
from pathlib import Path

from .curve import Market

#: Frozen illustrative configurations.
EXAMPLES: list[Market] = [
    Market("USDT", 800_000, 52_500, 900_000, 1),
    Market("SOL", 800_000, 100_000, 1_500_000, 1),
    Market("wBTC", 750_000, 60_000, 1_500_000, 1),
    Market("wETH", 750_000, 60_000, 1_500_000, 1),
]


def load(path: Path | None = None) -> list[Market]:
    """Load explicit JSON parameters or the frozen illustrative examples."""
    if path is None:
        return list(EXAMPLES)
    markets = json.loads(path.read_text())["markets"]
    return [
        Market(
            m["name"],
            m["optimal_utilization"],
            m["optimal_borrow_rate"],
            m["max_borrow_rate"],
            m["min_borrow_rate"] or 0,
        )
        for m in markets
    ]

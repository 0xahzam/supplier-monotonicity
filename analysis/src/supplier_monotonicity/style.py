"""Shared chart styling.

Inter is vendored under `assets/fonts` and registered with matplotlib at import
time, so output does not depend on what happens to be installed on the machine.
Charts render at 300 dpi and are written as PNG, PDF and SVG together.
"""

from __future__ import annotations

from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
from matplotlib import font_manager

ROOT = Path(__file__).resolve().parent.parent.parent
FONT_DIR = ROOT / "assets" / "fonts"
OUT = ROOT / "out"

INK = "#0b1220"
BODY = "#334155"
MUTED = "#7c8ba1"
GRID = "#e8edf3"
HAIRLINE = "#cbd5e1"
DANGER = "#d92d20"
GOOD = "#0b8a5c"
NEUTRAL = "#9aa8b8"

COLORS = {"USDT": "#0e7c6b", "SOL": "#6d3fd4", "wBTC": "#d9700a", "wETH": "#1f6feb"}
DASH = {"USDT": "-", "SOL": "-", "wBTC": "-", "wETH": (0, (5.5, 2.5))}

PCT = mpl.ticker.PercentFormatter(xmax=1.0, decimals=0)


def use() -> None:
    """Register the vendored fonts and set the house style."""
    for ttf in sorted(FONT_DIR.glob("*.ttf")):
        font_manager.fontManager.addfont(str(ttf))

    mpl.rcParams.update(
        {
            "figure.dpi": 300,
            "savefig.dpi": 300,
            "savefig.bbox": "tight",
            "savefig.pad_inches": 0.28,
            "figure.constrained_layout.use": True,
            "figure.constrained_layout.h_pad": 0.10,
            "figure.constrained_layout.w_pad": 0.12,
            "figure.facecolor": "white",
            "axes.facecolor": "white",
            # dollar signs in labels must not be read as mathtext delimiters
            "text.parse_math": False,
            "font.family": "Inter",
            "font.size": 8.5,
            "axes.labelsize": 8.5,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
            "text.color": BODY,
            "axes.labelcolor": BODY,
            "axes.labelpad": 7,
            "xtick.color": MUTED,
            "ytick.color": MUTED,
            "xtick.labelcolor": MUTED,
            "ytick.labelcolor": MUTED,
            "axes.grid": True,
            "axes.axisbelow": True,
            "grid.color": GRID,
            "grid.linewidth": 0.7,
            "axes.edgecolor": HAIRLINE,
            "axes.linewidth": 0.7,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "xtick.major.size": 0,
            "ytick.major.size": 0,
            "xtick.major.pad": 6,
            "ytick.major.pad": 5,
            "lines.solid_capstyle": "round",
            "lines.dash_capstyle": "round",
            "legend.frameon": False,
            "patch.linewidth": 0,
        }
    )


def figure(width: float = 11.0, height: float = 5.9):
    """One chart per figure, wide enough to read at full width in a document."""
    return plt.subplots(figsize=(width, height))


def title(ax, main: str, sub: str | None = None) -> None:
    """Title and caption stacked above the axes.

    Offsets are derived from the caption's line count instead of `set_title`,
    whose pad is measured from the axes and collides with anything else placed
    in the same band.
    """
    lines = sub.count("\n") + 1 if sub else 0
    base = 7
    if sub:
        ax.annotate(
            sub,
            xy=(0, 1),
            xytext=(0, base),
            xycoords="axes fraction",
            textcoords="offset points",
            fontsize=8,
            color=MUTED,
            va="bottom",
            ha="left",
            linespacing=1.5,
        )
    ax.annotate(
        main,
        xy=(0, 1),
        xytext=(0, base + 13.5 * lines + 5),
        xycoords="axes fraction",
        textcoords="offset points",
        fontsize=11.5,
        fontweight="semibold",
        color=INK,
        va="bottom",
        ha="left",
    )


def suptitle(fig, text: str) -> None:
    fig.suptitle(text, x=0.008, ha="left", fontsize=14.5, fontweight="bold", color=INK)


def end_labels(ax, entries, gap=0.045, dx=8):
    """Label curves at their right edge instead of using a legend.

    `entries` is a list of `(y_value, text, color)`. Series landing on the same
    value are merged into one label, and the rest are pushed apart vertically so
    nothing overlaps.
    """
    lo, hi = ax.get_ylim()
    log = ax.get_yscale() == "log"

    def to_frac(y):
        import math

        if log:
            return (math.log10(y) - math.log10(lo)) / (math.log10(hi) - math.log10(lo))
        return (y - lo) / (hi - lo)

    merged: list[list] = []
    for y, text, color in sorted(entries, key=lambda e: e[0]):
        f = to_frac(y)
        if merged and abs(f - merged[-1][0]) < 0.012:
            merged[-1][1] += " · " + text
            merged[-1][2] = NEUTRAL
        else:
            merged.append([f, text, color])

    for i in range(1, len(merged)):
        if merged[i][0] - merged[i - 1][0] < gap:
            merged[i][0] = merged[i - 1][0] + gap

    for f, text, color in merged:
        ax.annotate(
            text,
            xy=(1, min(f, 1.0)),
            xytext=(dx, 0),
            xycoords="axes fraction",
            textcoords="offset points",
            color=color,
            fontsize=8.5,
            fontweight="semibold",
            va="center",
            ha="left",
            annotation_clip=False,
        )


def save(fig, name: str) -> None:
    """Write the figure as PNG, and as PDF and SVG for anything that needs vector."""
    OUT.mkdir(exist_ok=True)
    (OUT / "vector").mkdir(exist_ok=True)
    fig.savefig(OUT / f"{name}.png")
    fig.savefig(OUT / "vector" / f"{name}.pdf")
    fig.savefig(OUT / "vector" / f"{name}.svg")
    plt.close(fig)

# Reproducible analysis

From this directory: `uv sync --locked`, `uv run --locked pytest tests -q`, then `uv run --locked python generate_figures.py`. Requires Python 3.12+; TeX Live provides the Latin Modern font. Inputs are frozen in `config/market.json`; no external checkout or network access is needed. Outputs are in `data/` and `../figures/`.

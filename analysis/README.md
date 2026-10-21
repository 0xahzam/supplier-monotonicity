# Reproducible analysis

From this directory: `uv sync --locked`, `uv run --locked pytest tests -q`, then `uv run --locked python generate_figures.py`. Requires Python 3.12+; TeX Live provides the Latin Modern font. Inputs are frozen in `config/market.json`; no external checkout or network access is needed. Outputs are in `data/` and `../figures/`.

## Drift market data

The evidence section uses two public Drift spot markets, USDC and SOL. Drift is a trading and lending protocol on Solana that records every change to a spot market as a program event. The snapshot in `data/drift/` was extracted once from those events, and the analysis reads only the snapshot, so it needs no network access.

`markets.csv.gz` holds the last `SpotInterestRecord` of each hour from 11 November 2024 to 1 April 2026. Each row has the market's scaled deposit and borrow balances, its cumulative deposit and borrow interest indices, and the rate curve parameters in force: optimal utilization, rate at the optimum and maximum rate.

`balances.csv.gz` holds, for each account and each hour with a deposit or withdrawal from 1 December 2025 to 1 April 2026, the account's balance after the last such event of the hour and before the first one, with the market interest indices at those events. It comes from the `DepositRecord` events, which carry the account's balance after each event from December 2025 on. Accounts are numbered, with no addresses. Subaccounts of one owner share a supplier number. The snapshot is pseudonymized, not anonymous: the balances and times are public onchain, so an account's history can be matched back to its address.

`suppliers.csv` marks each supplier that settled perpetual futures profit or loss in the same window, using the `SettlePnlRecord` events. Those suppliers hold deposits partly as trading collateral.

`src/supplier_monotonicity/drift.py` checks the rate curve against the interest the borrow index actually accrued, rebuilds supplier balances, and measures how often a supplier held more than the curve protected. `generate_figures.py` writes `data/drift/summary.json` and the figure. `tests/test_drift.py` pins the published results.

The same events are public onchain and can be extracted again from Solana history. This snapshot was read from an archive of them for convenience.

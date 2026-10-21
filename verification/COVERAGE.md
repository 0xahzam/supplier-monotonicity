# Equation and theorem coverage

Reference: `../build/main.tex`. **Proved** means a Lean theorem states the claim. **Supported** means Lean proves parts of the claim and the entry names the missing step. **Open** means the claim is not formalized. **Definition** marks a model input.

| ID | Source line | Status | Evidence / remaining obligation |
|---|---:|---|---|
| D001 | 86 | definition | Supply-rate definition; algebraic substitution U=B/T. |
| D002 | 90 | definition | Income model, encoded in Model.income. |
| D003 | 96 | definition | Resulting share, encoded in Model.share. |
| D004 | 102 | proved | utilization_hasDerivAt; smooth deposit path. |
| D005 | 114 | proved | income_hasDerivAt_raw and income_hasDerivAt. |
| D006 | 126 | proved | income_hasDerivAt / income_deriv. |
| D007 | 135 | proved | logarithmic_elasticity: derivative of log(R(exp x)). |
| D008 | 144 | proved | income_deriv. |
| D009 | 152 | proved | income_deriv_nonneg_iff. |
| D010 | 158 | proved | income_deriv_safe_share_iff; interior utilization. |
| D011 | 172 | proved | full_supplier_deriv. |
| D012 | 183 | proved | profile_all_shares_iff and envelope_iff, applied pointwise. |
| D013 | 197 | supported | logarithmic_elasticity and envelope_iff; normalized_rate_antitone and normalized_rate_bound establish the smooth boundary-ratio implication. General AC/a.e. integration remains open. |
| D014 | 205 | open | Locally absolutely continuous / a.e. admissible-family theorem not formalized. |
| D015 | 223 | definition | Fixed protection target definition; envelope_iff gives its pointwise consequence. |
| D016 | 231 | proved | power_boundary_derivative, power_boundary_elasticity, power_exp_matches_rpow. |
| D017 | 242 | supported | log_rate_integral_on proves smooth-interior log-rate FTC with integrability; full AC regularity remains open. |
| D018 | 252 | supported | smooth_endpoint_bound and power_hits_top; AC essential-supremum version remains open. |
| D019 | 263 | supported | safe_share_iff plus endpoint bound in smooth subclass; general endpoint theorem pending. |
| D020 | 274 | definition | Initial/final utilization; nonzero denominators made explicit. |
| D021 | 280 | proved | fresh_share. |
| D022 | 284 | proved | fresh_path_iff. |
| D023 | 293 | supported | fresh_all_starts_iff and fresh_share; explicit realization of every worst-case state not separately encoded. |
| D024 | 297 | proved | fresh_envelope and fresh_envelope_iff. |
| D025 | 301 | supported | hyperbolic_boundary_derivative and hyperbolic_boundary_elasticity; integrated uniqueness pending. |
| D026 | 321 | supported | fresh_base_positive checks consequence of bound; normalized_base_bound checks antitone endpoint step. Full limit argument pending. |
| D027 | 330 | definition | Slope between distinct kinks. |
| D028 | 334 | proved | fresh_linear_segment_iff and adjacent_fresh_ratio_iff; positive left rate and increasing kinks. |
| D029 | 350 | definition | Single-kink baseline; numerical endpoints checked. |
| D030 | 360 | supported | Exact rational sign bracket for quoted K=19 root; general root existence/uniqueness pending. |
| D031 | 366 | supported | Power branch elasticity and endpoint checks proved; full rejoin/greatest-minorant theorem pending. |
| D032 | 402 | proved | max_profile_envelope and combined_envelope; positive profiles. |
| D033 | 424 | supported | raise_recursion_minimal and raise_step_feasible; reverse indexing explicit; finite caps. |
| D034 | 438 | definition | Accumulated interest for integrable prescribed histories. |
| D035 | 442 | proved | accumulated_interest_difference and supplier_transfer; integrability explicit. |
| D036 | 467 | definition | Affine rate and elasticity substitution; endpoint theorem below. |
| D037 | 473 | proved | integer_endpoint_iff; fixed_linear_endpoint_suffices; continuous arithmetic, not rounded transactions. |
| D038 | 598 | proved | fresh_boundary_income_algebra together with Core derivative and fresh share. |
| D039 | 626 | proved | adjacent_fresh_ratio_iff. |
| D040 | 630 | proved | fixed_left_cap_iff, fixed_right_cap_iff, fixed_right_unbounded, fixed_left_zero, combined_envelope. |
| D041 | 641 | supported | floor_recursion_minimal; unbounded-cap limit handled numerically, not encoded in recursion theorem. |
| D042 | 649 | supported | lower_recursion_maximal; complete constructed-curve feasibility not yet assembled. |
| D043 | 676 | scope qualification | Normalized derivative equivalence, smooth antitonicity, running-infimum antitonicity and order bounds proved. The paper now assumes positive base rate; zero_base_flat_minorant explains why an unrestricted assertion is false. Continuity/regularity still pending. |
| D044 | 700 | supported | Power and hyperbolic branches checked separately; combined join, regularity and general K>0 domain not assembled. |
| D045 | 719 | supported | normalized_base_bound plus exact numerical check for K=19; general combined construction attainment pending. |
| D046 | 800 | supported | reconstructedRate_* proves positive C1 construction for continuous log-coordinate elasticity; reconstructed_utilization_elasticity gives eta. General local-profile extension, change of variables and full converse pending. |
| D047 | 812 | proved | continuous_rate_supremum_strict: positive continuous rate, interior differentiability, continuous derivative/rate quotient, and endpoint budget; explicit C1-data convention in Smoothing.lean. |
| D048 | 831 | definition | smoothEta; continuity and exact integral formally proved for w>0. |
| D049 | 847 | proved | smoothing_endpoint_unique for w>0; smooth_zero_width for the declared limiting value. |
| D050 | 854 | proved | smooth_plateau_derivative and smooth_plateau_derivative_positive. |
| D051 | 858 | proved | smoothing_ceiling_width_iff: full pointwise ceiling for w>0 and eta0<Kstar; w=0 is the separately declared limiting value. |
| D052 | 866 | proved | smoothEta_integral and smooth_area_identity. Corrected smoothing identity. |
| D053 | 873 | supported | smooth_ramp_primitive_derivative, smooth_primitive_join and reconstructedRate_*; C2 join assembly pending. |
| T001 | 124 | proved | Core derivative theorem at smooth states. |
| T002 | 202 | open | Full a.e. / locally absolutely continuous equivalence pending; no replacement by smooth result. |
| T003 | 249 | supported | Smooth endpoint bound and power attainment proved; AC essential-supremum theorem pending. |
| T004 | 290 | supported | Worst start, pointwise envelope, boundary derivative and finite-deposit lemmas proved; full theorem assembly and boundary uniqueness pending. |
| T005 | 809 | supported | Strict supremum statement proved directly in U using explicit C1 data; positive C1 reconstruction and width existence proved. Full assembled feasibility including all interval/join assumptions pending. |
| T006 | 844 | proved | Exact integral, plateau uniqueness, derivative, strictness and pointwise ceiling-width equivalence for nonzero width; zero width handled as the stated nonsmooth limit. |

Inline fragments, captions, tables and source blocks are hashed and counted but have no individual status.

Inventory counts (overlapping): `{'caption': 24, 'display': 53, 'inline': 535, 'source block': 157, 'table': 4, 'theorem/proposition': 6}`.

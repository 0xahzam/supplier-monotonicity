# Equation and theorem coverage

Reference: `../paper.tex`. **Supported** means proof components exist but the full claim is not yet certified. Definitions are model inputs, not proved economic facts. This table is not a whole-paper certificate.

| ID | Source line | Status | Evidence / remaining obligation |
|---|---:|---|---|
| D001 | 65 | definition | Supply-rate definition; algebraic substitution U=B/T. |
| D002 | 69 | definition | Income model, encoded in Core.income. |
| D003 | 73 | definition | Resulting share, encoded in Core.share. |
| D004 | 79 | proved | utilization_hasDerivAt; smooth deposit path. |
| D005 | 91 | proved | income_hasDerivAt_raw and income_hasDerivAt. |
| D006 | 103 | proved | income_hasDerivAt / income_deriv. |
| D007 | 112 | proved | logarithmic_elasticity: derivative of log(R(exp x)); ordinary notation correspondence reviewed manually. |
| D008 | 120 | proved | income_deriv. |
| D009 | 127 | proved | income_deriv_nonneg_iff. |
| D010 | 133 | proved | income_deriv_safe_share_iff; interior utilization. |
| D011 | 148 | proved | profile_all_shares_iff and envelope_iff, applied pointwise. |
| D012 | 159 | supported | logarithmic_elasticity and envelope_iff; normalized_rate_antitone and normalized_rate_bound establish the smooth boundary-ratio implication. General AC/a.e. integration remains open. |
| D013 | 167 | open | Locally absolutely continuous / a.e. admissible-family theorem not formalized. |
| D014 | 181 | supported | reconstructedRate_* proves positive C1 construction for continuous log-coordinate elasticity; reconstructed_utilization_elasticity gives eta. General local-profile extension, change of variables and full converse pending. |
| D015 | 192 | definition | Fixed protection target definition; envelope_iff gives its pointwise consequence. |
| D016 | 200 | proved | power_boundary_derivative, power_boundary_elasticity, power_exp_matches_rpow. |
| D017 | 211 | supported | log_rate_integral_on proves smooth-interior log-rate FTC with integrability; full AC regularity remains open. |
| D018 | 220 | supported | smooth_endpoint_bound and power_hits_top; AC essential-supremum version remains open. |
| D019 | 231 | supported | safe_share_iff plus endpoint bound in smooth subclass; general endpoint theorem pending. |
| D020 | 242 | definition | Initial/final utilization; nonzero denominators made explicit. |
| D021 | 248 | proved | fresh_share. |
| D022 | 252 | proved | fresh_path_iff. |
| D023 | 261 | supported | fresh_all_starts_iff and fresh_share; explicit realization of every worst-case state not separately encoded. |
| D024 | 265 | proved | fresh_envelope and fresh_envelope_iff. |
| D025 | 269 | supported | hyperbolic_boundary_derivative and hyperbolic_boundary_elasticity; integrated uniqueness pending. |
| D026 | 291 | supported | fresh_base_positive checks consequence of bound; normalized_base_bound checks antitone endpoint step. Full limit argument pending. |
| D027 | 302 | definition | Slope between distinct knots. |
| D028 | 306 | proved | fresh_linear_segment_iff and adjacent_fresh_ratio_iff; positive left rate and increasing knots. |
| D029 | 322 | definition | Single-kink baseline; numerical endpoints checked. |
| D030 | 332 | supported | Exact rational sign bracket for quoted K=19 root; general root existence/uniqueness pending. |
| D031 | 338 | supported | Power branch elasticity and endpoint checks proved; full rejoin/greatest-minorant theorem pending. |
| D032 | 349 | open | Informal eventual-equality limit claim; threshold and full piecewise construction not formalized. |
| D033 | 375 | proved | max_profile_envelope and combined_envelope; positive profiles. |
| D034 | 383 | supported | raise_recursion_minimal and raise_step_feasible; reverse indexing explicit; finite caps. |
| D035 | 405 | definition | Accumulated interest for integrable prescribed histories. |
| D036 | 409 | proved | accumulated_interest_difference and supplier_transfer; integrability explicit. |
| D037 | 443 | definition | Affine rate and elasticity substitution; endpoint theorem below. |
| D038 | 449 | proved | integer_endpoint_iff; fixed_linear_endpoint_suffices; continuous arithmetic, not rounded transactions. |
| D039 | 530 | proved | fresh_boundary_income_algebra together with Core derivative and fresh share. |
| D040 | 579 | proved | Duplicate of D033. |
| D041 | 587 | proved | adjacent_fresh_ratio_iff. |
| D042 | 591 | proved | fixed_left_cap_iff, fixed_right_cap_iff, fixed_right_unbounded, fixed_left_zero, combined_envelope. |
| D043 | 602 | supported | floor_recursion_minimal; unbounded-cap limit handled numerically, not encoded in recursion theorem. |
| D044 | 608 | supported | raise_recursion_minimal and raise_step_feasible. |
| D045 | 615 | supported | lower_recursion_maximal; complete constructed-curve feasibility not yet assembled. |
| D046 | 642 | scope qualification | Normalized derivative equivalence, smooth antitonicity, running-infimum antitonicity and order bounds proved. The paper now assumes positive base rate; zero_base_flat_minorant explains why an unrestricted assertion is false. Continuity/regularity still pending. |
| D047 | 666 | supported | Power and hyperbolic branches checked separately; combined join, regularity and general K>0 domain not assembled. |
| D048 | 685 | supported | normalized_base_bound plus exact numerical check for K=19; general combined construction attainment pending. |
| D049 | 762 | proved | Duplicate of D010. |
| D050 | 775 | supported | Duplicate of D014; log-coordinate construction proved, full local-profile formulation pending. |
| D051 | 785 | proved | continuous_rate_supremum_strict: positive continuous rate, interior differentiability, continuous derivative/rate quotient, and endpoint budget; explicit C1-data convention in Endpoint.lean. |
| D052 | 804 | definition | smoothEta; continuity and exact integral formally proved for w>0. |
| D053 | 820 | proved | smoothing_endpoint_unique for w>0; smooth_zero_width for the declared limiting value. |
| D054 | 827 | proved | smooth_plateau_derivative and smooth_plateau_derivative_positive. |
| D055 | 831 | proved | smoothing_ceiling_width_iff: full pointwise ceiling for w>0 and eta0<Kstar; w=0 is the separately declared limiting value. |
| D056 | 839 | proved | smoothEta_integral and smooth_area_identity. Corrected smoothing identity. |
| D057 | 846 | supported | smooth_ramp_primitive_derivative, smooth_primitive_join and reconstructedRate_*; C2 join assembly pending. |
| D058 | 890 | proved | full_supplier_deriv. |
| T001 | 101 | proved | Core derivative theorem at smooth states. |
| T002 | 164 | open | Full a.e. / locally absolutely continuous equivalence pending; no replacement by smooth result. |
| T003 | 217 | supported | Smooth endpoint bound and power attainment proved; AC essential-supremum theorem pending. |
| T004 | 258 | supported | Worst start, pointwise envelope, boundary derivative and finite-deposit lemmas proved; full theorem assembly and boundary uniqueness pending. |
| T005 | 782 | supported | Strict supremum statement proved directly in U using explicit C1 data; positive C1 reconstruction and width existence proved. Full assembled feasibility including all interval/join assumptions pending. |
| T006 | 817 | proved | Exact integral, plateau uniqueness, derivative, strictness and pointwise ceiling-width equivalence for nonzero width; zero width handled as the stated nonsmooth limit. |

Inline fragments, captions, tables and source blocks are indexed during verification but are not individually certified.

Inventory counts (overlapping): `{'caption': 25, 'inline': 542, 'table': 3, 'source block': 154, 'display': 58, 'theorem/proposition': 6}`.

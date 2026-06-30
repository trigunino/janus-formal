# Janus Agent Handoff

Purpose: give any future AI agent a clean starting point for Janus work without rereading the whole corpus blindly.

## Start Here

1. Read `docs/janus_knowledge_base.md` for the map.
2. Open the relevant card in `docs/source_cards/`.
3. Check `docs/verified_formula_register.md` before relying on any formula.
4. Follow `docs/toolchain.md` for source -> formalization -> code -> data work.
5. Use `python scripts/search_janus_library.py "query" --ref M18` for source-local checks.
6. Verify every new equation against the local PDF before promoting it to `docs/source_traceability.md` or code.

## Evidence Rules

- Keep source ID, equation number and document status together.
- Do not mix peer-reviewed anchors, HAL mirrors, books and author documents as if they had the same evidential weight.
- Mark phenomenological fits separately from Janus-derived formulas.
- If Janus is used as an axiom, state that explicitly and search for the missing map from Janus assumptions to observables.

## Current High-Value Anchors

- `M15`: coupled field equations and signed-mass interaction logic.
- `M18`: SN/open-distance formulas and exact expansion parameterization.
- `M30`: modern bimetric/geodesic formulation.
- `M31`: symmetry/torsor formalism.
- `X2026-variable-constants`: variable-constants hypothesis, especially Eq. 40.
- `X2026-expansion-desi`: current DESI-oriented expansion target.

## Current P0 Closure Entry Point

Start from `outputs/reports/p0_scross_candidate_triage_matrix.md`.
It narrows the non-rustine `S_cross` search to two families:

- source-derived derivative solder action;
- source-derived BF/constraint transport action.

Then use `outputs/reports/p0_pt_lie_vjanus_ajanus_constraint_solver.md`.
It removes PT/Lie-forbidden polynomial branches:

- `V_Janus` must be even in the minimal solder coordinate;
- `A_Janus` must follow the selected P-like or PT-like parity branch.

Then use `outputs/reports/p0_ajanus_branch_selector_dynamics_gate.md`.
The weak-field non-equal relative-curvature rows require linear residual matching,
so the PT-like even branch is rejected in that branch and the P-like odd branch remains.
The remaining task is to promote this weak-field gate to full covariant source/action closure.
Use `outputs/reports/p0_ajanus_covariant_lift_obligation.md` for that step:
the surviving branch needs `a1=r1` and `a3=r3`, where `r1/r3` must be source-derived.
Use `outputs/reports/p0_covariant_q_field_candidate_gate.md` before reducing this to a scalar:
the current candidate is the relative strain tensor `Q`, while determinant/log-volume is only a trace diagnostic.
Use `outputs/reports/p0_relative_strain_q_regular_branch_gate.md` for its current concrete branch:
`Q=1/2 log(H)` with mirror inverse `Q -> -Q`; this still needs source-selected regularity and derivative closure.
Use `outputs/reports/p0_relative_strain_dh_lgeom_vs_lorentz_gate.md` to avoid a false closure:
pure Lorentz `Omega_alpha` gives `D H=0`; nontrivial `Q` needs the source-derived eta-symmetric strain part of `D L_geom`.
Use `outputs/reports/p0_sigma_dh_equivalence_gate.md` before adding any strain field:
`Sigma_alpha` and `D H` are equivalent source-selection variables, not two independent knobs.
Use `outputs/reports/p0_sigma_source_selector_attack_matrix.md` for the current source route triage:
no route selects `Sigma/DH` yet; nonmetricity, Stueckelberg and BF remain conditional.
Use `outputs/reports/p0_sigma_source_traceability_gap_gate.md` before citing a published Janus source for this:
current traceability has no explicit `N_alpha`, `Phi_Sigma`, `D_alpha H` or `Sigma_alpha` equation.
Use `outputs/reports/p0_sigma_trace_only_no_go_gate.md` before using determinant/B4vol:
trace data cannot select the 4D trace-free strain channel.
Use `outputs/reports/p0_tracefree_h_projector_gate.md` to isolate the rank-9 `H_TF/Q_TF` channel.
Use `outputs/reports/p0_tracefree_h_projector_variation_dependency_gate.md` before dropping projector-variation terms:
fixed-projector, covariant `H` and screen-congruence branches are distinct.
Use `outputs/reports/p0_tracefree_h_source_candidate_matrix.md` before accepting tensor/action routes:
anisotropic stress, Weyl/shear, Vlasov quadrupole, relative strain action and BF/GL remain candidates only.
Use `p0_tracefree_h_irrep_source_requirements_gate` and
`p0_tracefree_h_action_operator_requirements_gate` before claiming any `Q_TF` source is structurally valid.
Use `p0_tracefree_h_closure_obligation_matrix` as the exact target:
derive `P_STF(E_H - S_TF^Janus)=0` from Janus before prediction.
Use `p0_tracefree_h_scalar_vector_no_go_gate` to reject scalar/vector shortcuts and
`p0_tracefree_h_variational_source_template_gate` as the action-variation template.
Use `p0_tracefree_h_variational_action_basis_gate`,
`p0_tracefree_h_action_basis_el_variation_gate`,
`p0_tracefree_h_action_measure_variation_gate`,
`p0_tracefree_h_frechet_log_adjoint_gate`,
`p0_tracefree_h_qtf_to_h_chain_rule_gate`,
`p0_tracefree_h_quadratic_qtf_h_el_gate`,
`p0_tracefree_h_linear_qtf_xtf_h_el_gate`,
`p0_same_l_spin_connection_transport_identity_gate`,
`p0_same_l_bridge_induces_m_k_qcross_gate`,
`p0_tracefree_h_janus_coupled_stress_stf_transport_gate`,
`p0_tracefree_h_xtf_source_provenance_variation_contract`,
`p0_tracefree_h_action_basis_acceptance_filter`,
`p0_tracefree_h_linear_coupling_rank_gate`,
`p0_tracefree_h_derivative_branch_stability_gate`,
`p0_tracefree_h_linear_xtf_provenance_gate`,
`p0_tracefree_h_same_bridge_dependency_gate`,
`p0_tracefree_h_source_action_provenance_chain_gate` and `p0_tracefree_h_derivation_attack_plan`
before attempting the next `S_TF^Janus` derivation.
Use the action-measure variation gate before dropping `delta_mu` terms:
measure variation cannot be promoted to a trace-free source by itself.
Use the chain-rule gate before converting a formal `Q_TF` variation into an `H` equation:
`delta Q` is a Frechet matrix-log variation, and `H^{-1} delta H` is only a proved commuting-branch shortcut.
Use the FrechetLog adjoint gate before treating a `Q_TF` gradient as an `H` gradient:
off-diagonal divided-difference coefficients cannot be dropped outside a proved commuting branch.
Use the quadratic Q_TF H-EL gate before accepting `Tr(Q_TF^2)`:
it gives a formal homogeneous H-gradient, not a Janus source by itself.
Use the linear Q_TF X_TF H-EL gate before accepting a nonzero source:
`X_TF` must be Janus-derived, same-bridge, and varied with its dependencies.
Use the X_TF provenance contract as the primary non-rustine source route:
try `P_STF(T_self + B4vol T_other_to_self)` from M15/M30 before any new tensor.
Use the coupled-stress STF transport gate before claiming this route closes:
the 4D STF type is coherent, but the common bridge `M/L` remains source-open.
Use the candidate subgates before promoting tensor diagnostics:
`p0_tracefree_h_anisotropic_stress_gate`, `p0_tracefree_h_weyl_shear_source_gate`,
`p0_tracefree_h_vlasov_quadrupole_gate`, `p0_tracefree_h_relative_strain_action_gate`,
and `p0_tracefree_h_bf_gl_phi_sigma_gate`.
Use `outputs/reports/p0_tracefree_h_isotropy_no_go_gate.md` before accepting scalar/FLRW closure:
density, pressure, determinant and exact FLRW data do not select perturbative `Q_TF`.
Use `outputs/reports/p0_h_strain_action_variation_gate.md` before accepting an `H` action:
ultralocal `V(H)` is algebraic only; derivative `D H` dynamics need source and ghost gates.
Use `outputs/reports/p0_h_strain_ghost_symbolic_gate.md` for the derivative `H/Q_TF` sign screen:
`k_t>0`, `k_x>0`, `m^2>=0` are required before any source-derived action can be accepted.
Use `outputs/reports/p0_nonmetricity_integrability_curl_gate.md` before accepting any `N_alpha` source:
it must integrate to one same `H` and pass the mirror branch, not contain a fitted curl defect.
Use `outputs/reports/p0_nonmetricity_curl_numeric_probe.md` only as diagnostic support for the curl gate.
Use `outputs/reports/p0_nonmetricity_mirror_inverse_gate.md` before treating minus-sector nonmetricity:
`N_mirror = D(H^{-1})` is induced by the same `H`, not an independent source.
Use `outputs/reports/p0_phi_sigma_source_action_decision_gate.md` and
`outputs/reports/p0_nonmetricity_source_acceptance_criteria.md` before promoting any `N/Phi_Sigma` branch.
Use `outputs/reports/p0_nonmetricity_rank_reduction_ledger.md` to keep the remaining source target precise:
after trace/mirror/integrability accounting, the open physical channel is trace-free `H/Q_TF`.
Use the three focused gates before claiming progress on that triage:
`p0_relative_metric_nonmetricity_sigma_dh_gate`, `p0_stueckelberg_sigma_dh_variation_rank_gate`,
and `p0_cartan_bf_gl_strain_selector_gate`.
Use `outputs/reports/p0_relative_strain_q_derivative_omega_gate.md` before differentiating it:
`DQ` must be the Frechet derivative of the matrix log from the same `Omega_alpha`; the scalar `H^{-1}DH` shortcut is allowed only on a proved commuting branch.

Do not introduce a new `S_cross`, `Phi_R`, `L`, `Q_det` or `Q_cross` branch unless it passes the non-rustine kernel and ghost/stability gate.
Relevant reports: `p0_non_rustine_closure_research_kernel.md`, `p0_action_ghost_stability_gate.md`, `p0_minimal_janus_soldering_principle_candidate.md`.

## Known Weak Point

`M26` currently has a weak/empty text extraction. Use the PDF directly before relying on that card.

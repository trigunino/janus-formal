from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_tracefree_h_closure_obligation_matrix import (
    build_payload as build_obligations,
)
from scripts.build_p0_tracefree_h_action_basis_acceptance_filter import (
    build_payload as build_action_basis_filter,
)
from scripts.build_p0_tracefree_h_action_basis_el_variation_gate import (
    build_payload as build_el_variation,
)
from scripts.build_p0_tracefree_h_action_measure_variation_gate import (
    build_payload as build_action_measure_variation,
)
from scripts.build_p0_tracefree_h_frechet_log_adjoint_gate import (
    build_payload as build_frechet_log_adjoint,
)
from scripts.build_p0_tracefree_h_qtf_to_h_chain_rule_gate import (
    build_payload as build_qtf_to_h_chain_rule,
)
from scripts.build_p0_tracefree_h_quadratic_qtf_h_el_gate import (
    build_payload as build_quadratic_qtf_h_el,
)
from scripts.build_p0_tracefree_h_xtf_source_provenance_variation_contract import (
    build_payload as build_xtf_source_contract,
)
from scripts.build_p0_tracefree_h_derivative_branch_stability_gate import (
    build_payload as build_derivative_branch,
)
from scripts.build_p0_tracefree_h_linear_coupling_rank_gate import (
    build_payload as build_linear_coupling,
)
from scripts.build_p0_tracefree_h_linear_qtf_xtf_h_el_gate import (
    build_payload as build_linear_qtf_xtf_h_el,
)
from scripts.build_p0_tracefree_h_janus_coupled_stress_stf_transport_gate import (
    build_payload as build_janus_coupled_stress_stf_transport,
)
from scripts.build_p0_tracefree_h_linear_xtf_provenance_gate import (
    build_payload as build_linear_xtf,
)
from scripts.build_p0_tracefree_h_same_bridge_dependency_gate import (
    build_payload as build_same_bridge_dependency,
)
from scripts.build_p0_tracefree_h_source_action_provenance_chain_gate import (
    build_payload as build_source_action_provenance,
)
from scripts.build_p0_tracefree_h_variational_action_basis_gate import (
    build_payload as build_action_basis,
)
from scripts.build_p0_tracefree_h_variational_source_template_gate import (
    build_payload as build_variational_template,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_derivation_attack_plan.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_derivation_attack_plan.json")


def build_payload() -> dict:
    obligations = build_obligations()
    variational = build_variational_template()
    action_basis = build_action_basis()
    el_variation = build_el_variation()
    action_measure_variation = build_action_measure_variation()
    frechet_adjoint = build_frechet_log_adjoint()
    qtf_to_h_chain_rule = build_qtf_to_h_chain_rule()
    quadratic_qtf_h_el = build_quadratic_qtf_h_el()
    xtf_source_contract = build_xtf_source_contract()
    action_filter = build_action_basis_filter()
    linear_coupling = build_linear_coupling()
    coupled_stress_transport = build_janus_coupled_stress_stf_transport()
    linear_qtf_xtf_h_el = build_linear_qtf_xtf_h_el()
    derivative_branch = build_derivative_branch()
    linear_xtf = build_linear_xtf()
    same_bridge_dependency = build_same_bridge_dependency()
    source_action_provenance = build_source_action_provenance()
    branches = [
        {
            "branch": "source_variation",
            "target": "derive P_STF(delta S_Janus/delta H)=0",
            "requires": "accepted S_Janus[H,L,phi,matter] variation domain",
            "accepted": bool(source_action_provenance["source_action_provenance_closed"]),
        },
        {
            "branch": "linear_coupling",
            "target": "derive an allowed int Q_TF^{ab} X_TF_ab source term",
            "requires": "X_TF source-derived, covariant STF, same bridge",
            "accepted": bool(
                linear_coupling["any_candidate_accepted"]
                and linear_xtf["any_candidate_accepted"]
                and same_bridge_dependency["source_provenance_closed"]
            ),
        },
        {
            "branch": "derivative_operator",
            "target": "derive P_STF(E_H) from DQ_TF or DH_TF action",
            "requires": "boundary/gauge, principal symbol, stability and curl integrability",
            "accepted": bool(derivative_branch["accepted_branch_supplied"]),
        },
        {
            "branch": "bf_gl_constraint",
            "target": "derive Phi_Sigma/N_alpha as a Janus BF/GL source equation",
            "requires": "not pure topological BF; local H_TF dynamics and same-L transport",
            "accepted": False,
        },
    ]
    return {
        "description": "Attack plan for deriving the trace-free H/Q_TF source equation without adding a rustine.",
        "status": "tracefree-h-derivation-attack-plan-open",
        "target_equation": obligations["target_equation"],
        "template_equations": variational["target_source_equations"],
        "action_basis_terms": [row["term"] for row in action_basis["candidate_terms"]],
        "action_basis_accepted": bool(action_basis["any_term_accepted"]),
        "formal_variations_recorded": bool(el_variation["all_variations_formal"]),
        "action_measure_variation_artifact": "p0_tracefree_h_action_measure_variation_gate",
        "action_measure_variation_ready": bool(action_measure_variation["measure_variation_closed"]),
        "frechet_log_adjoint_artifact": "p0_tracefree_h_frechet_log_adjoint_gate",
        "frechet_log_adjoint_ready": bool(frechet_adjoint["source_provenance_closed"]),
        "qtf_to_h_chain_rule_artifact": "p0_tracefree_h_qtf_to_h_chain_rule_gate",
        "qtf_to_h_chain_rule_ready": bool(qtf_to_h_chain_rule["qtf_to_h_variation_ready"]),
        "qtf_to_h_chain_rule_status": qtf_to_h_chain_rule["status"],
        "quadratic_qtf_h_el_artifact": "p0_tracefree_h_quadratic_qtf_h_el_gate",
        "quadratic_qtf_h_el_ready": bool(quadratic_qtf_h_el["accepted_as_closure"]),
        "linear_qtf_xtf_h_el_artifact": "p0_tracefree_h_linear_qtf_xtf_h_el_gate",
        "linear_qtf_xtf_h_el_ready": bool(linear_qtf_xtf_h_el["accepted_as_closure"]),
        "xtf_source_contract_artifact": "p0_tracefree_h_xtf_source_provenance_variation_contract",
        "xtf_source_contract_ready": bool(xtf_source_contract["contract_closed"]),
        "best_xtf_candidate": xtf_source_contract["best_non_rustine_candidate"],
        "coupled_stress_transport_artifact": "p0_tracefree_h_janus_coupled_stress_stf_transport_gate",
        "coupled_stress_transport_algebra_closed": bool(
            coupled_stress_transport["algebraic_transport_closed"]
        ),
        "coupled_stress_transport_acceptance_closed": bool(
            coupled_stress_transport["transport_acceptance_closed"]
        ),
        "same_l_bridge_stack_artifact": coupled_stress_transport["same_l_bridge_stack_artifact"],
        "same_l_bridge_stack_algebra_closed": bool(
            coupled_stress_transport["same_l_bridge_stack_algebra_closed"]
        ),
        "same_l_bridge_stack_source_selected": bool(
            coupled_stress_transport["same_l_bridge_stack_source_selected"]
        ),
        "action_filter_accepts_branch": bool(action_filter["any_class_accepted"]),
        "best_next_branch": action_filter["best_next_branch"],
        "derivative_branch_ready": bool(derivative_branch["accepted_branch_supplied"]),
        "linear_xtf_provenance_ready": bool(linear_xtf["any_candidate_accepted"]),
        "same_bridge_dependency_ready": bool(same_bridge_dependency["source_provenance_closed"]),
        "source_action_provenance_ready": bool(source_action_provenance["source_action_provenance_closed"]),
        "linear_coupling_accepted": bool(linear_coupling["any_candidate_accepted"]),
        "branches": branches,
        "branches_total": len(branches),
        "branches_accepted": sum(1 for row in branches if row["accepted"]),
        "negative_progress": [
            "scalar/vector low-derivative shortcuts rejected",
            "determinant trace kept out of Q_TF",
            "residual target source forbidden",
        ],
        "next_math_tasks": [
            "write candidate S_Janus term before computing residuals",
            "compute delta S/delta H and project with P_STF",
            "close or explicitly carry action-measure delta_mu terms before using H EL equations",
            "fix FrechetLog_H adjoint branch before using Q_TF gradients as H gradients",
            "pull Q_TF variations back to H with FrechetLog_H before accepting an H equation",
            "use quadratic Q_TF H-EL gate only as formal algebra until Janus source provenance exists",
            "try the Janus coupled stress STF contract as the primary non-rustine X_TF route",
            "use the coupled-stress transport gate algebra, then close its source-selected bridge",
            "use linear Q_TF X_TF H-EL gate only if X_TF provenance and dependency terms close",
            "check boundary/gauge and same-L assumptions before accepting the EL equation",
            "run ghost/stability screen for any derivative H/Q branch",
        ],
        "accepted_as_prediction_input": False,
        "source_selection_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The admissible next move is a variational derivation, not a fitted "
            "source. Each branch must produce P_STF(delta S_Janus/delta H)=0 or "
            "P_STF(E_H-S_TF)=0 before it can affect predictions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Derivation Attack Plan",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target equation: `{payload['target_equation']}`",
        f"Branches accepted: {payload['branches_accepted']}/{payload['branches_total']}",
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Template Equations",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["template_equations"])
    lines.extend(["", "## Action Basis Terms", ""])
    lines.extend(f"- `{item}`" for item in payload["action_basis_terms"])
    lines.extend(
        [
            "",
            "## Action Filter",
            "",
            f"- formal variations recorded: `{payload['formal_variations_recorded']}`",
            f"- action measure variation artifact: `{payload['action_measure_variation_artifact']}`",
            f"- action measure variation ready: `{payload['action_measure_variation_ready']}`",
            f"- FrechetLog adjoint artifact: `{payload['frechet_log_adjoint_artifact']}`",
            f"- FrechetLog adjoint ready: `{payload['frechet_log_adjoint_ready']}`",
            f"- Q_TF to H chain rule artifact: `{payload['qtf_to_h_chain_rule_artifact']}`",
            f"- Q_TF to H chain rule ready: `{payload['qtf_to_h_chain_rule_ready']}`",
            f"- Q_TF to H chain rule status: `{payload['qtf_to_h_chain_rule_status']}`",
            f"- quadratic Q_TF H-EL artifact: `{payload['quadratic_qtf_h_el_artifact']}`",
            f"- quadratic Q_TF H-EL ready: `{payload['quadratic_qtf_h_el_ready']}`",
            f"- linear Q_TF X_TF H-EL artifact: `{payload['linear_qtf_xtf_h_el_artifact']}`",
            f"- linear Q_TF X_TF H-EL ready: `{payload['linear_qtf_xtf_h_el_ready']}`",
            f"- X_TF source contract artifact: `{payload['xtf_source_contract_artifact']}`",
            f"- X_TF source contract ready: `{payload['xtf_source_contract_ready']}`",
            f"- best X_TF candidate: `{payload['best_xtf_candidate']}`",
            f"- coupled-stress transport artifact: `{payload['coupled_stress_transport_artifact']}`",
            f"- coupled-stress transport algebra closed: `{payload['coupled_stress_transport_algebra_closed']}`",
            f"- coupled-stress transport acceptance closed: `{payload['coupled_stress_transport_acceptance_closed']}`",
            f"- same-L bridge stack artifact: `{payload['same_l_bridge_stack_artifact']}`",
            f"- same-L bridge stack algebra closed: `{payload['same_l_bridge_stack_algebra_closed']}`",
            f"- same-L bridge stack source selected: `{payload['same_l_bridge_stack_source_selected']}`",
            f"- action filter accepts branch: `{payload['action_filter_accepts_branch']}`",
            f"- best next branch: `{', '.join(payload['best_next_branch']['classes'])}`",
            f"- allowed now: `{payload['best_next_branch']['allowed_now']}`",
            f"- derivative branch ready: `{payload['derivative_branch_ready']}`",
            f"- linear X_TF provenance ready: `{payload['linear_xtf_provenance_ready']}`",
            f"- same bridge dependency ready: `{payload['same_bridge_dependency_ready']}`",
            f"- source/action provenance ready: `{payload['source_action_provenance_ready']}`",
        ]
    )
    lines.extend(["", "## Branches", "", "| branch | target | requires | accepted |", "|---|---|---|---:|"])
    for row in payload["branches"]:
        lines.append(f"| {row['branch']} | {row['target']} | {row['requires']} | {row['accepted']} |")
    lines.extend(["", "## Negative Progress", ""])
    lines.extend(f"- {item}" for item in payload["negative_progress"])
    lines.extend(["", "## Next Math Tasks", ""])
    lines.extend(f"- {item}" for item in payload["next_math_tasks"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

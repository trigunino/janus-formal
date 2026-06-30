from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_tracefree_h_frechet_log_adjoint_gate import (
    build_payload as build_frechet_log_adjoint,
)
from scripts.build_p0_tracefree_h_action_measure_variation_gate import (
    build_payload as build_action_measure_variation,
)
from scripts.build_p0_tracefree_h_linear_xtf_provenance_gate import (
    build_payload as build_linear_xtf_provenance,
)
from scripts.build_p0_tracefree_h_janus_coupled_stress_stf_transport_gate import (
    build_payload as build_janus_coupled_stress_stf_transport,
)
from scripts.build_p0_tracefree_h_xtf_source_provenance_variation_contract import (
    build_payload as build_xtf_source_contract,
)
from scripts.build_p0_tracefree_h_projector_variation_dependency_gate import (
    build_payload as build_projector_variation_dependency,
)
from scripts.build_p0_tracefree_h_same_bridge_dependency_gate import (
    build_payload as build_same_bridge_dependency,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_linear_qtf_xtf_h_el_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_linear_qtf_xtf_h_el_gate.json")


def build_payload() -> dict:
    frechet = build_frechet_log_adjoint()
    measure = build_action_measure_variation()
    xtf = build_linear_xtf_provenance()
    coupled_stress_transport = build_janus_coupled_stress_stf_transport()
    xtf_contract = build_xtf_source_contract()
    projector = build_projector_variation_dependency()
    same_bridge = build_same_bridge_dependency()
    derivation_steps = [
        {
            "step": "candidate_density",
            "formula": "L_lin = Q_TF^{ab} X_TF_ab",
            "status": "formal candidate only",
        },
        {
            "step": "qtf_variation",
            "formula": "delta_Q L_lin = <X_TF, delta Q_TF>",
            "status": "formal",
        },
        {
            "step": "base_h_source",
            "formula": "G_H^base = 1/2 L_log,H^*[P_STF(X_TF)]",
            "status": "formal source shape",
        },
        {
            "step": "dependency_variation",
            "formula": "delta_X L_lin = Q_TF^{ab} delta X_TF_ab",
            "status": "required when X_TF depends on H,L,phi,matter",
        },
        {
            "step": "full_el_shape",
            "formula": "G_H^base + deltaX + deltaP_STF + delta_mu terms = 0",
            "status": "not accepted until X_TF is Janus-derived",
        },
    ]
    blockers = [
        "X_TF provenance is open: no candidate is source-derived covariant STF rank-2 same-bridge data",
        "same-bridge dependency is open for Q_TF and X_TF",
        "projector variation terms remain open unless a fixed-projector branch is proved",
        "measure variation delta_mu must be fixed by B4vol/J/lapse branch",
        "residual X_TF cancellation is forbidden",
    ]
    return {
        "description": "Bounded P0 gate for the formal H Euler term induced by Q_TF X_TF.",
        "status": "tracefree-h-linear-qtf-xtf-h-el-gate-open",
        "target_channel": "H_TF/Q_TF",
        "candidate_density": "Q_TF^{ab} X_TF_ab",
        "formal_nonzero_source_shape_recorded": True,
        "base_h_source": "1/2 L_log,H^*[P_STF(X_TF)]",
        "best_xtf_candidate": xtf_contract["best_non_rustine_candidate"],
        "best_xtf_source_shape": xtf_contract["best_candidate_source_shape"],
        "coupled_stress_transport_algebra_closed": bool(
            coupled_stress_transport["algebraic_transport_closed"]
        ),
        "coupled_stress_transport_acceptance_closed": bool(
            coupled_stress_transport["transport_acceptance_closed"]
        ),
        "frechet_log_adjoint_ready": bool(frechet["source_provenance_closed"]),
        "xtf_source_contract_closed": bool(xtf_contract["contract_closed"]),
        "xtf_provenance_closed": bool(xtf["source_selection_closed"]),
        "same_bridge_closed": bool(same_bridge["source_provenance_closed"]),
        "projector_dependency_closed": bool(projector["projector_dependency_closed"]),
        "action_measure_variation_closed": bool(measure["measure_variation_closed"]),
        "dependency_terms_required": True,
        "residual_xtf_allowed": False,
        "janus_source_action_provenance": False,
        "accepted_as_closure": False,
        "accepted_as_prediction_input": False,
        "derivation_steps": derivation_steps,
        "blockers": blockers,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The linear Q_TF X_TF coupling gives the right formal nonzero H-source "
            "shape, 1/2 L_log,H^*[P_STF(X_TF)]. It remains non-predictive because "
            "X_TF, same-bridge dependency, projector terms and measure terms are not "
            "Janus-closed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Linear Q_TF X_TF H EL Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Candidate density: `{payload['candidate_density']}`",
        f"Formal nonzero source shape recorded: {payload['formal_nonzero_source_shape_recorded']}",
        f"Base H source: `{payload['base_h_source']}`",
        f"Best X_TF candidate: `{payload['best_xtf_candidate']}`",
        f"Best X_TF source shape: `{payload['best_xtf_source_shape']}`",
        f"Coupled-stress transport algebra closed: {payload['coupled_stress_transport_algebra_closed']}",
        f"Coupled-stress transport acceptance closed: {payload['coupled_stress_transport_acceptance_closed']}",
        f"FrechetLog adjoint ready: {payload['frechet_log_adjoint_ready']}",
        f"X_TF source contract closed: {payload['xtf_source_contract_closed']}",
        f"X_TF provenance closed: {payload['xtf_provenance_closed']}",
        f"Same bridge closed: {payload['same_bridge_closed']}",
        f"Projector dependency closed: {payload['projector_dependency_closed']}",
        f"Action measure variation closed: {payload['action_measure_variation_closed']}",
        f"Dependency terms required: {payload['dependency_terms_required']}",
        f"Residual X_TF allowed: {payload['residual_xtf_allowed']}",
        f"Janus source/action provenance: {payload['janus_source_action_provenance']}",
        f"Accepted as closure: {payload['accepted_as_closure']}",
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Steps",
        "",
        "| step | formula | status |",
        "|---|---|---|",
    ]
    for row in payload["derivation_steps"]:
        lines.append(f"| {row['step']} | `{row['formula']}` | {row['status']} |")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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

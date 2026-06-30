from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_tracefree_h_anisotropic_stress_gate import (
    build_payload as build_anisotropic_stress,
)
from scripts.build_p0_tracefree_h_action_operator_requirements_gate import (
    build_payload as build_action_operator_requirements,
)
from scripts.build_p0_tracefree_h_bf_gl_phi_sigma_gate import (
    build_payload as build_bf_gl_phi_sigma,
)
from scripts.build_p0_tracefree_h_irrep_source_requirements_gate import (
    build_payload as build_irrep_requirements,
)
from scripts.build_p0_tracefree_h_projector_variation_dependency_gate import (
    build_payload as build_projector_variation_dependency,
)
from scripts.build_p0_tracefree_h_relative_strain_action_gate import (
    build_payload as build_relative_strain_action,
)
from scripts.build_p0_tracefree_h_vlasov_quadrupole_gate import (
    build_payload as build_vlasov_quadrupole,
)
from scripts.build_p0_tracefree_h_weyl_shear_source_gate import (
    build_payload as build_weyl_shear,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_source_candidate_matrix.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_source_candidate_matrix.json")


def build_payload() -> dict:
    anisotropic_stress = build_anisotropic_stress()
    weyl_shear = build_weyl_shear()
    vlasov_quadrupole = build_vlasov_quadrupole()
    relative_strain_action = build_relative_strain_action()
    bf_gl_phi_sigma = build_bf_gl_phi_sigma()
    irrep_requirements = build_irrep_requirements()
    action_operator_requirements = build_action_operator_requirements()
    projector_variation_dependency = build_projector_variation_dependency()
    candidates = [
        {
            "candidate": "janus_coupled_stress_stf",
            "selects_q_tf": "conditional",
            "janus_source_or_action": False,
            "accepted": False,
            "requires": "derive P_STF(T_self + B4vol T_other_to_self) on the same bridge from M15/M30 source tensors",
            "blocker": "verified coupled source exists, but transport, H-variation, same bridge and measure are not closed",
            "subgate": "p0_tracefree_h_xtf_source_provenance_variation_contract",
            "subgate_prediction_ready": False,
        },
        {
            "candidate": "anisotropic_stress_pi_tf",
            "selects_q_tf": "conditional",
            "janus_source_or_action": False,
            "accepted": False,
            "requires": "Janus matter source/action deriving Pi_TF as the trace-free H source",
            "blocker": "Pi_TF is plausible tensor data but not yet a Janus-selected Q_TF law",
            "subgate": "p0_tracefree_h_anisotropic_stress_gate",
            "subgate_prediction_ready": bool(anisotropic_stress["prediction_ready"]),
        },
        {
            "candidate": "weyl_shear",
            "selects_q_tf": "conditional",
            "janus_source_or_action": False,
            "accepted": False,
            "requires": "Janus optical/metric source action tying Weyl/shear to Q_TF",
            "blocker": "Weyl/shear is diagnostic until its source equation is derived",
            "subgate": "p0_tracefree_h_weyl_shear_source_gate",
            "subgate_prediction_ready": bool(weyl_shear["prediction_ready"]),
        },
        {
            "candidate": "kinetic_quadrupole_vlasov",
            "selects_q_tf": "conditional",
            "janus_source_or_action": False,
            "accepted": False,
            "requires": "Janus Vlasov moment/action closure selecting the quadrupole source",
            "blocker": "kinetic quadrupole needs a closed Janus moment hierarchy",
            "subgate": "p0_tracefree_h_vlasov_quadrupole_gate",
            "subgate_prediction_ready": bool(vlasov_quadrupole["prediction_ready"]),
        },
        {
            "candidate": "relative_metric_strain_action",
            "selects_q_tf": "conditional",
            "janus_source_or_action": False,
            "accepted": False,
            "requires": "accepted relative-H/strain action whose EL equation sources Q_TF",
            "blocker": "candidate action has not passed source, rank, and stability gates",
            "subgate": "p0_tracefree_h_relative_strain_action_gate",
            "subgate_prediction_ready": bool(relative_strain_action["prediction_ready"]),
        },
        {
            "candidate": "bf_gl_phi_sigma",
            "selects_q_tf": "conditional",
            "janus_source_or_action": False,
            "accepted": False,
            "requires": "BF/GL Janus source term Phi_Sigma or N_alpha for symmetric strain",
            "blocker": "Phi_Sigma remains an unaccepted source/action target",
            "subgate": "p0_tracefree_h_bf_gl_phi_sigma_gate",
            "subgate_prediction_ready": bool(bf_gl_phi_sigma["prediction_ready"]),
        },
    ]
    rejected = [
        {
            "candidate": "density_scalar",
            "accepted": False,
            "reason": "scalar density cannot select rank-9 trace-free H data",
        },
        {
            "candidate": "pressure_scalar",
            "accepted": False,
            "reason": "isotropic pressure is scalar trace data, not Pi_TF",
        },
        {
            "candidate": "b4vol_determinant",
            "accepted": False,
            "reason": "B4vol/determinant fixes only volume trace",
        },
        {
            "candidate": "isotropic_flrw",
            "accepted": False,
            "reason": "isotropic FLRW has no trace-free source channel",
        },
        {
            "candidate": "residual_fit",
            "accepted": False,
            "reason": "fit-by-residual is not a Janus source/action",
        },
    ]
    accepted_candidates = [
        row["candidate"]
        for row in candidates
        if row["accepted"] and row["janus_source_or_action"]
    ]
    return {
        "description": (
            "Bounded P0 matrix for trace-free H/Q_TF source candidates and "
            "explicit rejected scalar/fit routes."
        ),
        "status": "tracefree-h-source-candidate-matrix-open",
        "qtf_channel": "Q_TF / trace-free H rank-9 source selector",
        "acceptance_rule": "no candidate accepted without Janus source/action",
        "candidates": candidates,
        "rejected_routes": rejected,
        "candidate_count": len(candidates),
        "rejected_count": len(rejected),
        "subgates": [
            "p0_tracefree_h_irrep_source_requirements_gate",
            "p0_tracefree_h_action_operator_requirements_gate",
            "p0_tracefree_h_projector_variation_dependency_gate",
            "p0_tracefree_h_janus_coupled_stress_stf_transport_gate",
            "p0_tracefree_h_xtf_source_provenance_variation_contract",
            "p0_tracefree_h_anisotropic_stress_gate",
            "p0_tracefree_h_weyl_shear_source_gate",
            "p0_tracefree_h_vlasov_quadrupole_gate",
            "p0_tracefree_h_relative_strain_action_gate",
            "p0_tracefree_h_bf_gl_phi_sigma_gate",
        ],
        "source_requirement_gates": {
            "irrep_source_requirement_closed": bool(irrep_requirements["source_selection_closed"]),
            "action_operator_requirement_closed": bool(action_operator_requirements["requirements_closed"]),
            "projector_variation_dependency_closed": bool(
                projector_variation_dependency["projector_dependency_closed"]
            ),
        },
        "subgates_prediction_ready": False,
        "accepted_candidates": accepted_candidates,
        "any_candidate_accepted": bool(accepted_candidates),
        "source_selection_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not promote scalar density, pressure, determinant, or B4vol into Q_TF",
            "do not accept isotropic FLRW as trace-free strain source",
            "do not use residual fitting as source selection",
            "require Janus source/action before accepting any Q_TF candidate",
        ],
        "verdict": (
            "The viable-looking tensor/action routes remain candidates only. "
            "No trace-free H source is accepted until a Janus source/action derives it."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Source Candidate Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Q_TF channel: {payload['qtf_channel']}",
        f"Acceptance rule: {payload['acceptance_rule']}",
        f"Candidates: {payload['candidate_count']}",
        f"Rejected routes: {payload['rejected_count']}",
        f"Any candidate accepted: {payload['any_candidate_accepted']}",
        f"Source selection closed: {payload['source_selection_closed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidates",
        "",
        "| candidate | selects Q_TF | Janus source/action | accepted | subgate | blocker |",
        "|---|---:|---:|---:|---|---|",
    ]
    for row in payload["candidates"]:
        lines.append(
            f"| {row['candidate']} | {row['selects_q_tf']} | "
            f"{row['janus_source_or_action']} | {row['accepted']} | "
            f"{row.get('subgate', '')} | {row['blocker']} |"
        )
    lines.extend(["", "## Source Requirement Gates", ""])
    for key, value in payload["source_requirement_gates"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Subgates", ""])
    lines.extend(f"- `{item}`" for item in payload["subgates"])
    lines.extend(
        [
            "",
            "## Rejected Routes",
            "",
            "| candidate | accepted | reason |",
            "|---|---:|---|",
        ]
    )
    for row in payload["rejected_routes"]:
        lines.append(f"| {row['candidate']} | {row['accepted']} | {row['reason']} |")
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
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

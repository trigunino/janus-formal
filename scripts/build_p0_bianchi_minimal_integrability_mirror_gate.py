from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_bianchi_minimal_integrability_mirror_gate.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_minimal_integrability_mirror_gate.json")


def build_payload() -> dict:
    gates = [
        {
            "gate": "flow_lift",
            "condition": "D_u L=Omega_u_min L with Omega_u_min fixed by the Bianchi-minimal branch",
            "closed": True,
            "status": "local-flow-only",
        },
        {
            "gate": "full_connection_lift",
            "condition": "extend Omega_u_min to eta-antisymmetric Omega_alpha for all receiver directions",
            "closed": False,
            "status": "transverse derivatives not selected",
        },
        {
            "gate": "curvature_integrability",
            "condition": "D_[alpha Omega_beta]+[Omega_alpha,Omega_beta] matches the relative spin-curvature obstruction",
            "closed": False,
            "status": "required before a global L field exists",
        },
        {
            "gate": "mirror_inverse",
            "condition": "L_plus_to_minus=L_minus_to_plus^{-1} and mirrored Omega laws close both Bianchi rows",
            "closed": False,
            "status": "not proved by the local plus-branch solution",
        },
        {
            "gate": "same_l_qcross",
            "condition": "Q_cross uses the same L and covectors as K transport",
            "closed": False,
            "status": "must be checked after mirror/integrability",
        },
    ]
    required_equations = [
        "Omega_alpha_AB=-Omega_alpha_BA",
        "D_alpha L=Omega_alpha L",
        "D_[alpha Omega_beta]+[Omega_alpha,Omega_beta] = relative curvature obstruction",
        "L_plus_to_minus=L_minus_to_plus^{-1}",
        "Omega_inverse_alpha=-L^{-1} Omega_alpha L plus sector-connection conversion terms",
    ]
    return {
        "description": (
            "Promotion gate for the Bianchi-minimal joint branch. It tests whether the "
            "local flow solution can become a full mirrored cross-sector transport law."
        ),
        "status": "integrability-mirror-gate-open",
        "depends_on": "p0_bianchi_minimal_joint_dl_dlogb_solution",
        "gates": gates,
        "required_equations": required_equations,
        "local_flow_solution_available": True,
        "full_connection_lift_closed": False,
        "curvature_integrability_closed": False,
        "mirror_inverse_closed": False,
        "same_l_qcross_closed": False,
        "rank_one_dust_only": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The joint branch gives a non-fitted local flow solution. It becomes physics "
            "only if it lifts to a full eta-antisymmetric Omega_alpha, passes the curvature "
            "integrability condition, mirrors under L^{-1}, and uses the same L for Q_cross."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi-Minimal Integrability Mirror Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Local flow solution available: {payload['local_flow_solution_available']}",
        f"Full connection lift closed: {payload['full_connection_lift_closed']}",
        f"Curvature integrability closed: {payload['curvature_integrability_closed']}",
        f"Mirror inverse closed: {payload['mirror_inverse_closed']}",
        f"Same L Q_cross closed: {payload['same_l_qcross_closed']}",
        f"Rank-one dust only: {payload['rank_one_dust_only']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Gates",
        "",
        "| gate | condition | closed | status |",
        "|---|---|---|---|",
    ]
    for row in payload["gates"]:
        lines.append(f"| {row['gate']} | `{row['condition']}` | {row['closed']} | {row['status']} |")
    lines.extend(["", "## Required Equations", ""])
    lines.extend(f"- `{item}`" for item in payload["required_equations"])
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

from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_beta_vec_closure_gate.md")
JSON_PATH = Path("outputs/reports/janus_linear_beta_vec_closure_gate.json")


def build_payload() -> dict:
    closure_matrix = [
        {"gate": "linear_transfer_growth", "required": "T_s,D_s,theta_s from Janus operator", "closed": False},
        {"gate": "background_omegas", "required": "Omega_plus(a), Omega_minus_eff(a) source-derived", "closed": False},
        {"gate": "amplitude", "required": "A_J source-backed or explicit no-fit", "closed": False},
        {"gate": "density_branch", "required": "delta_minus convention fixed against Q_det", "closed": False},
        {"gate": "beta_provenance", "required": "source_derived_janus_dynamics", "closed": False},
        {"gate": "transport_map", "required": "Lorentz-compatible L_minus_to_plus", "closed": False},
        {"gate": "same_map", "required": "same L for K_plus/K_minus and Q_cross", "closed": False},
        {"gate": "residuals", "required": "R_plus=0 and R_minus=0", "closed": False},
    ]
    existing_surfaces = [
        "janus_linear_ic_equations_target",
        "janus_velocity_ic_closure_target",
        "p0_source_derived_beta_reconstruction_target",
        "p0_stueckelberg_beta_field_provenance_gate",
        "p0_stueckelberg_beta_vec_u_transport_target",
        "p0_l_k_qcross_consistency_target",
    ]
    return {
        "description": "Closure gate for allowing beta_vec provenance source_derived_janus_dynamics.",
        "status": "closure-gate-open",
        "closure_matrix": closure_matrix,
        "existing_surfaces": existing_surfaces,
        "source_derived_beta_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The beta label source_derived_janus_dynamics is forbidden until every "
            "linear, map, and residual gate closes."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear Beta Vec Closure Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source-derived beta allowed: {payload['source_derived_beta_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Closure Matrix",
        "",
        "| gate | required | closed |",
        "|---|---|---|",
    ]
    for row in payload["closure_matrix"]:
        lines.append(f"| {row['gate']} | {row['required']} | {row['closed']} |")
    lines.extend(["", "## Existing Surfaces", ""])
    lines.extend(f"- `{item}`" for item in payload["existing_surfaces"])
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

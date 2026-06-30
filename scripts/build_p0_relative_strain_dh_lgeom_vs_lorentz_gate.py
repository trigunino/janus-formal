from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_l_transport_candidate_geometry import (
    build_payload as build_l_candidates,
)


REPORT_PATH = Path("outputs/reports/p0_relative_strain_dh_lgeom_vs_lorentz_gate.md")
JSON_PATH = Path("outputs/reports/p0_relative_strain_dh_lgeom_vs_lorentz_gate.json")


def build_payload() -> dict:
    l_candidates = build_l_candidates()
    return {
        "description": "Gate separating the raw L_geom strain derivative from pure Lorentz transport.",
        "status": "dh-identity-closed-strain-source-open",
        "depends_on": ["p0_l_transport_candidate_geometry"],
        "h_definition": "H=eta^{-1} L_geom^T eta L_geom",
        "raw_transport_definition": "D_alpha L_geom = Gamma_alpha L_geom",
        "eta_adjoint": "Gamma_alpha^dagger_eta = eta^{-1} Gamma_alpha^T eta",
        "dh_identity": (
            "D_alpha H = eta^{-1} L_geom^T eta "
            "(Gamma_alpha^dagger_eta + Gamma_alpha) L_geom"
        ),
        "eta_symmetric_part": "Sigma_alpha=1/2(Gamma_alpha+Gamma_alpha^dagger_eta)",
        "dh_from_strain": "D_alpha H = 2 eta^{-1} L_geom^T eta Sigma_alpha L_geom",
        "lorentz_generator_case": {
            "condition": "Omega_alpha^dagger_eta=-Omega_alpha",
            "consequence": "D_alpha H=0 for D_alpha L_geom=Omega_alpha L_geom",
            "meaning": "pure Lorentz transport rotates frames but does not change relative strain Q",
        },
        "implications": [
            "nontrivial Q transport needs a source-derived eta-symmetric strain generator Sigma_alpha",
            "the Lorentz-projected L can still be the same K/Q_cross map, but Q is built from raw L_geom strain",
            "do not identify Omega_alpha with the strain generator unless Janus source proves a non-Lorentz Gamma_alpha",
            "do not fit Sigma_alpha to force A_Janus or R_plus/R_minus cancellation",
        ],
        "candidate_context": [row["name"] for row in l_candidates["candidates"]],
        "dh_identity_closed": True,
        "lorentz_omega_alone_gives_nontrivial_dh": False,
        "strain_generator_required": True,
        "strain_generator_source_selected": False,
        "dq_closed": False,
        "prediction_ready": False,
        "notable_improvement": (
            "The algebraic D H identity is closed. The remaining physics is sharply "
            "localized to source-selecting the eta-symmetric strain generator Sigma_alpha."
        ),
        "remaining_lock": (
            "Derive Gamma_alpha/Sigma_alpha from Janus source geometry or prove that "
            "the allowed branch has Sigma_alpha=0, which would make this Q transport trivial."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Relative Strain D H: L_geom vs Lorentz Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"H definition: `{payload['h_definition']}`",
        f"Raw transport: `{payload['raw_transport_definition']}`",
        f"Eta adjoint: `{payload['eta_adjoint']}`",
        f"D H identity closed: {payload['dh_identity_closed']}",
        f"Lorentz Omega alone gives nontrivial D H: {payload['lorentz_omega_alone_gives_nontrivial_dh']}",
        f"Strain generator required: {payload['strain_generator_required']}",
        f"Strain generator source selected: {payload['strain_generator_source_selected']}",
        f"DQ closed: {payload['dq_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
        f"- `{payload['dh_identity']}`",
        f"- `{payload['eta_symmetric_part']}`",
        f"- `{payload['dh_from_strain']}`",
        "",
        "## Pure Lorentz Case",
        "",
    ]
    for key, value in payload["lorentz_generator_case"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Implications", ""])
    lines.extend(f"- {item}" for item in payload["implications"])
    lines.extend(["", "## Candidate Context", ""])
    lines.extend(f"- `{item}`" for item in payload["candidate_context"])
    lines.extend(["", "## Result", "", payload["notable_improvement"], ""])
    lines.extend([f"Remaining lock: {payload['remaining_lock']}", ""])
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

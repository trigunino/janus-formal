from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_relative_strain_dh_lgeom_vs_lorentz_gate import (
    build_payload as build_dh_gate,
)
from scripts.build_p0_relative_strain_q_derivative_omega_gate import (
    build_payload as build_dq_gate,
)


REPORT_PATH = Path("outputs/reports/p0_sigma_dh_equivalence_gate.md")
JSON_PATH = Path("outputs/reports/p0_sigma_dh_equivalence_gate.json")


def build_payload() -> dict:
    dh_gate = build_dh_gate()
    dq_gate = build_dq_gate()
    return {
        "description": "Gate proving Sigma_alpha and D_alpha H are the same unresolved source choice.",
        "status": "sigma-dh-equivalence-closed-source-selection-open",
        "depends_on": [
            "p0_relative_strain_dh_lgeom_vs_lorentz_gate",
            "p0_relative_strain_q_derivative_omega_gate",
        ],
        "forward_identity": dh_gate["dh_from_strain"],
        "inverse_identity": (
            "Gamma_alpha+Gamma_alpha^dagger_eta = "
            "eta^{-1} L_geom^{-T} eta (D_alpha H) L_geom^{-1}; "
            "Sigma_alpha=1/2 eta^{-1} L_geom^{-T} eta (D_alpha H) L_geom^{-1}"
        ),
        "dq_identity": dq_gate["matrix_log_derivative"],
        "equivalence_rules": [
            "choosing Sigma_alpha chooses D_alpha H",
            "choosing D_alpha H chooses the eta-symmetric part Sigma_alpha",
            "the eta-antisymmetric Lorentz part remains separate and cannot change H",
            "there is no independent Sigma_alpha and D_alpha H freedom",
        ],
        "allowed_source_selectors": [
            "published Janus source equation for raw L_geom or relative metric strain",
            "variational equation for Gamma_alpha/Sigma_alpha from an accepted action",
            "relative curvature/nonmetricity identity derived before observational comparison",
            "boundary/gauge condition stated as part of the Janus branch, not fitted afterward",
        ],
        "forbidden_moves": [
            "set Sigma_alpha to cancel R_plus/R_minus after computing residuals",
            "fit D_alpha H or Q coefficients to lensing/power amplitudes",
            "add an independent Q connection when L_geom/Gamma already defines D H",
            "use pure Lorentz Omega_alpha as nontrivial strain transport",
        ],
        "identity_closed": True,
        "sigma_is_independent_knob": False,
        "source_selection_closed": False,
        "prediction_ready": False,
        "notable_improvement": (
            "The open variable is reduced to one source selector: either Janus derives "
            "D_alpha H, or equivalently it derives Sigma_alpha. They cannot be chosen separately."
        ),
        "remaining_lock": (
            "Find a Janus source/action/relative-curvature identity selecting this single "
            "strain channel without observational fitting."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Sigma / D H Equivalence Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Identity closed: {payload['identity_closed']}",
        f"Sigma is independent knob: {payload['sigma_is_independent_knob']}",
        f"Source selection closed: {payload['source_selection_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
        f"- forward: `{payload['forward_identity']}`",
        f"- inverse: `{payload['inverse_identity']}`",
        f"- DQ: `{payload['dq_identity']}`",
        "",
        "## Equivalence Rules",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["equivalence_rules"])
    lines.extend(["", "## Allowed Source Selectors", ""])
    lines.extend(f"- {item}" for item in payload["allowed_source_selectors"])
    lines.extend(["", "## Forbidden Moves", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_moves"])
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

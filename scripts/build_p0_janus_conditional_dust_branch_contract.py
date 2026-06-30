from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_conditional_dust_branch_contract.md")
JSON_PATH = Path("outputs/reports/p0_janus_conditional_dust_branch_contract.json")


def build_payload() -> dict:
    required_conditions = [
        "p_plus=p_minus=0",
        "Pi_plus^{AB}=Pi_minus^{AB}=0",
        "dust density convention uses B_4vol exactly once",
        "G0i dust beta inversion denominators are nonzero",
        "same-L branch is L=I for comoving scalar or shift-derived Lorentz boost for non-comoving dust",
        "R_plus/R_minus residual checks remain explicit",
    ]
    allowed_outputs = [
        "conditional weak-field scalar Phi/Psi branch",
        "conditional transverse G0i beta inversion",
        "diagnostic PM/Green-kernel mode handling",
        "no survey or tensor prediction label",
    ]
    forbidden_outputs = [
        "general perfect-fluid closure",
        "anisotropic-stress closure",
        "fitted Q_det/Q_cross correction",
        "sigma8/S8 normalization claim",
        "using dust branch when p or Pi terms are nonzero",
    ]
    return {
        "description": "Acceptance contract for using the Janus weak-field dust branch conditionally.",
        "status": "conditional-dust-branch-contract-open",
        "depends_on": [
            "p0_janus_g0i_dust_beta_inversion_target",
            "p0_janus_matter_eos_pi_branch_decision",
            "p0_janus_eos_pi_source_audit",
        ],
        "required_conditions": required_conditions,
        "allowed_outputs": allowed_outputs,
        "forbidden_outputs": forbidden_outputs,
        "dust_conditions_explicit": True,
        "dust_branch_diagnostic_ready": True,
        "dust_branch_general_physics_ready": False,
        "residuals_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The dust branch may be used for bounded diagnostics only when every listed condition "
            "is declared. It is not a substitute for EOS/Pi closure or survey prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Conditional Dust Branch Contract",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dust conditions explicit: {payload['dust_conditions_explicit']}",
        f"Dust branch diagnostic ready: {payload['dust_branch_diagnostic_ready']}",
        f"Dust branch general physics ready: {payload['dust_branch_general_physics_ready']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Required Conditions",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["required_conditions"])
    lines.extend(["", "## Allowed Outputs", ""])
    lines.extend(f"- {item}" for item in payload["allowed_outputs"])
    lines.extend(["", "## Forbidden Outputs", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_outputs"])
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

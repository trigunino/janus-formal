from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_kids1000_janus_holst_green_kernel_closure_checklist import build_payload as build_green_checklist
    from scripts.build_kids1000_janus_holst_no_fit_boundary import build_payload as build_no_fit_boundary
    from scripts.build_p0_eft_growth_kink_mu_functions import build_payload as build_kink_mu_payload
    from scripts.build_p0_eft_growth_kink_solver_target import build_payload as build_kink_solver_payload
    from scripts.build_p0_eft_kink_lensing_growth_bridge import build_payload as build_kink_bridge_payload
    from scripts.build_p0_eft_slip_jump_derivation_check import build_payload as build_jump_payload
except ModuleNotFoundError:
    from build_kids1000_janus_holst_green_kernel_closure_checklist import build_payload as build_green_checklist
    from build_kids1000_janus_holst_no_fit_boundary import build_payload as build_no_fit_boundary
    from build_p0_eft_growth_kink_mu_functions import build_payload as build_kink_mu_payload
    from build_p0_eft_growth_kink_solver_target import build_payload as build_kink_solver_payload
    from build_p0_eft_kink_lensing_growth_bridge import build_payload as build_kink_bridge_payload
    from build_p0_eft_slip_jump_derivation_check import build_payload as build_jump_payload


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_kink_lensing_target.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_kink_lensing_target.json")


def build_payload() -> dict:
    boundary = build_no_fit_boundary()
    green = build_green_checklist()
    jump = build_jump_payload()
    bridge = build_kink_bridge_payload()
    kink_mu = build_kink_mu_payload()
    solver = build_kink_solver_payload()
    return {
        "description": "KiDS-1000 target for the Janus-Holst kink-only lensing branch.",
        "status": "kink-lensing-target-open",
        "why": "value-slip Green response is scheme-dependent; kink-only uses the derivative jump directly.",
        "kids_symptom_reference": boundary["dominant_failure"],
        "value_slip_status": {
            "green_kernel_computed": green["green_kernel_computed"],
            "can_enable_value_slip": green["can_enable_value_slip"],
        },
        "closed_inputs": {
            "derivative_jump_slip_source_closed": jump["theorem_status"]["derivative_jump_slip_source_closed"],
            "lensing_kink_ready_conditionally": bridge["theorem_status"]["lensing_kink_ready_conditionally"],
            "skink_formula_encoded": kink_mu["theorem_status"]["skink_formula_encoded"],
            "kink_jump_condition_encoded": solver["theorem_status"]["kink_jump_condition_encoded"],
        },
        "open_inputs": {
            "skink_coefficient_derived": kink_mu["theorem_status"]["skink_coefficient_derived"],
            "alpha_Janus_derived": kink_mu["theorem_status"]["alpha_Janus_derived"],
            "growth_solver_implemented": solver["theorem_status"]["growth_solver_implemented"],
            "full_cosmology_prediction_ready": bridge["theorem_status"]["full_cosmology_prediction_ready"],
        },
        "target_operator": {
            "input": "Delta(partial_n(Psi-Phi)) from source-derived jump equations",
            "output": "kink/refraction correction to positive-photon optical projection",
            "feeds": "lensing projection and/or growth jump S_kink, not algebraic eta_slip",
            "does_not_use": "coincident Green kernel, Z_MID_BIN2, bin factors, KiDS residual scalars",
        },
        "acceptance_tests": [
            "derive S_kink coefficient from Euler/geodesic projection before KiDS comparison",
            "derive alpha_Janus(a) from transported active stress",
            "implement no-fit kink projection or growth ODE",
            "run KiDS without value-slip Green kernel, bin shifts or bin factors",
        ],
        "forbidden_shortcuts": boundary["forbidden_uses"]
        + [
            "replace kink projection by fitted eta_slip",
            "choose S_kink coefficient from pair 2-3 residuals",
            "use the scheme-dependent Green response as a value-slip coefficient",
        ],
        "gate": "kink_lensing_projection",
        "gate_closed": False,
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Kink-Only Lensing Target",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Gate: `{payload['gate']}`",
        f"Gate closed: `{payload['gate_closed']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        payload["why"],
        "",
        "## Target Operator",
        "",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["target_operator"].items())
    lines.extend(["", "## Closed Inputs", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["closed_inputs"].items())
    lines.extend(["", "## Open Inputs", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["open_inputs"].items())
    lines.extend(["", "## Acceptance Tests", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_tests"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.append("")
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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

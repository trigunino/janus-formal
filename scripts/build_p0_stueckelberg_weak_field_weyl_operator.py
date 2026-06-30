from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_weak_field_weyl_operator.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_weak_field_weyl_operator.json")


def build_payload() -> dict:
    operator = {
        "metric_scope": "weak-field positive optical metric potential",
        "input": "Phi_lens_plus on a 2D screen or thin-lens slice",
        "convergence": "kappa = 1/2 (partial_xx + partial_yy) Phi_lens_plus",
        "weyl_gamma1": "gamma1 = 1/2 (partial_xx - partial_yy) Phi_lens_plus",
        "weyl_gamma2": "gamma2 = partial_xy Phi_lens_plus",
        "code_surface": "janus_lab.lensing.weak_field_weyl_screen_tidal_components_2d",
    }
    obligations = [
        "derive Phi_lens_plus from delta G_plus[h_plus], not from survey shear",
        "keep Ricci convergence and Weyl trace-free shear as separate outputs",
        "forbid Q_cross or Q_det absorption of gamma1/gamma2 residuals",
        "attach observer/source gauge and affine normalization before ray integration",
        "compare to PM reduced Ricci diagnostic only after provenance is declared",
    ]
    decision = {
        "weak_field_weyl_operator_available": True,
        "metric_potential_source_derived": False,
        "weyl_trace_free_output_available": True,
        "full_tensor_weyl_closed": False,
        "prediction_ready": False,
        "reason": (
            "The screen Weyl/tidal operator is executable for a declared weak-field "
            "metric potential. It does not derive that potential from the coupled "
            "Janus equations, so it cannot yet unlock survey-level predictions."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_weak_field_weyl_operator",
        "status": "weak-field-weyl-operator-diagnostic",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "operator": operator,
        "obligations": obligations,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Weak Field Weyl Operator",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Operator",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["operator"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Weak-field Weyl operator available: {decision['weak_field_weyl_operator_available']}",
            f"Metric potential source-derived: {decision['metric_potential_source_derived']}",
            f"Weyl trace-free output available: {decision['weyl_trace_free_output_available']}",
            f"Full tensor Weyl closed: {decision['full_tensor_weyl_closed']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")

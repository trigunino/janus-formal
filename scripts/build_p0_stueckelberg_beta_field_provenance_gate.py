from __future__ import annotations

import json
from pathlib import Path

from janus_lab.lensing import beta_field_is_prediction_ready, validate_beta_field_provenance


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_beta_field_provenance_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_beta_field_provenance_gate.json")


def build_payload() -> dict:
    rows = [
        {
            "provenance": "declared_physical_velocity",
            "valid": True,
            "prediction_ready": beta_field_is_prediction_ready("declared_physical_velocity"),
            "use": "diagnostic declared velocity field",
        },
        {
            "provenance": "pm_hubble_calibrated_diagnostic",
            "valid": True,
            "prediction_ready": beta_field_is_prediction_ready("pm_hubble_calibrated_diagnostic"),
            "use": "PM velocity converted with explicit H0^-1 calibration",
        },
        {
            "provenance": "source_derived_janus_dynamics",
            "valid": True,
            "prediction_ready": beta_field_is_prediction_ready("source_derived_janus_dynamics"),
            "use": "target state after Janus transfer/growth/velocity closure",
        },
    ]
    forbidden = ["survey_fit", "shear_fit", "sigma8_fit", "s8_fit"]
    decision = {
        "beta_field_gate_defined": True,
        "pm_calibrated_beta_usable_as_diagnostic": True,
        "source_derived_beta_available": False,
        "noncomoving_source_identity_closed": False,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_beta_field_provenance_gate",
        "status": "beta-field-provenance-gate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "rows": rows,
        "forbidden": forbidden,
        "code_surfaces": [
            "janus_lab.lensing.validate_beta_field_provenance",
            "janus_lab.lensing.beta_field_is_prediction_ready",
            "janus_lab.lensing.positive_noncomoving_t00_source_grid",
        ],
        "decision": decision,
        "sanity_check": validate_beta_field_provenance("pm_hubble_calibrated_diagnostic"),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Beta Field Provenance Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| provenance | valid | prediction ready | use |",
        "|---|---|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['provenance']} | {row['valid']} | {row['prediction_ready']} | {row['use']} |"
        )
    lines.extend(["", "## Forbidden"])
    lines.extend(f"- `{item}`" for item in payload["forbidden"])
    lines.extend(["", "## Code Surfaces"])
    lines.extend(f"- `{item}`" for item in payload["code_surfaces"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Beta field gate defined: {decision['beta_field_gate_defined']}",
            f"PM calibrated beta usable as diagnostic: {decision['pm_calibrated_beta_usable_as_diagnostic']}",
            f"Source-derived beta available: {decision['source_derived_beta_available']}",
            f"Noncomoving source identity closed: {decision['noncomoving_source_identity_closed']}",
            f"Prediction ready: {decision['prediction_ready']}",
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

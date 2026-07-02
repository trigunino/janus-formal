from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_nonlinear_boundary_variation_obligation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_nonlinear_boundary_variation_obligation_gate.json")


def build_payload() -> dict:
    obligations = {
        "linear_boundary_residual_cancelled": True,
        "determinant_boundary_residual_cancelled": True,
        "volume_solder_counterterm_inserted": True,
        "orientation_single_z4_geometry_fixed": True,
        "nonlinear_tetrad_boundary_variation_computed": False,
        "cartan_connection_boundary_variation_computed": False,
        "membrane_junction_variation_computed": False,
        "gauge_fixed_boundary_variation_unique": False,
        "boundary_second_variation_residual_vanishing": False,
    }
    closed = all(obligations.values())
    return {
        "status": "janus-z4-nonlinear-boundary-variation-obligation-gate",
        "boundary_obligations": obligations,
        "nonlinear_boundary_prerequisites_ready": all(
            obligations[key]
            for key in (
                "linear_boundary_residual_cancelled",
                "determinant_boundary_residual_cancelled",
                "volume_solder_counterterm_inserted",
                "orientation_single_z4_geometry_fixed",
            )
        ),
        "full_nonlinear_boundary_variation_closed": closed,
        "remaining_boundary_obligations": [
            key for key, value in obligations.items() if not value
        ],
        "pure_math_model_closed_without_axioms": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required_gate": "derive_full_tetrad_connection_membrane_boundary_variation",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Nonlinear Boundary Variation Obligation Gate",
        "",
        f"Prerequisites ready: `{payload['nonlinear_boundary_prerequisites_ready']}`",
        f"Full nonlinear boundary variation closed: `{payload['full_nonlinear_boundary_variation_closed']}`",
        "",
        "## Remaining boundary obligations",
    ]
    lines.extend(f"- `{item}`" for item in payload["remaining_boundary_obligations"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

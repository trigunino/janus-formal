from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_counterterm_radial_projection import (
    build_counterterm_radial_projection_formula,
)


TRANSPORT_PATH = Path("outputs/active_z2_sigma/counterterm_tetrad_transport_closure.json")
COEFF_PATH = Path("outputs/active_z2_sigma/counterterm_residual_coefficients_partial.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_radial_projection_formula.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_projection_formula.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_projection_formula.json")


def build_payload(
    *,
    transport_path: Path = TRANSPORT_PATH,
    coeff_path: Path = COEFF_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = transport_path.exists() and coeff_path.exists()
    output_written = False
    validation_error = None
    formula: dict | None = None
    if input_exists:
        try:
            transport = json.loads(transport_path.read_text(encoding="utf-8"))
            coeff = json.loads(coeff_path.read_text(encoding="utf-8"))
            formula = build_counterterm_radial_projection_formula(
                dimension=int(transport["dimension"]),
                torsion_coefficient_ready=bool(coeff["R_T_A_ready"]),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(formula, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-radial-projection-formula",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {
            "transport_closure": str(transport_path),
            "partial_coefficients": str(coeff_path),
        },
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "output_written": output_written,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "formula": formula or {},
        "next_required": []
        if output_written
        else ["derive counterterm tetrad transport and partial residual coefficients"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    formula = payload["formula"]
    lines = [
        "# Janus Z2/Sigma Counterterm Radial Projection Formula",
        "",
        f"Output written: `{payload['output_written']}`",
    ]
    if formula:
        lines.extend(
            [
                f"partial_R L_ct: `{formula['reduced_radial_derivative']}`",
                f"E_counterterm: `{formula['E_counterterm_formula']}`",
                f"Still requires: `{formula['still_requires_for_values']}`",
            ]
        )
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_counterterm_residual_coefficients import (
    build_partial_counterterm_residual_coefficients,
)


TORSION_PATH = Path("outputs/active_z2_sigma/torsion_pullback_components_inputs.json")
IRREDUCIBLE_PATH = Path("outputs/active_z2_sigma/flrw_irreducible_torsion_components.json")
HOLST_PATH = Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json")
IMMIRZI_SCALAR_PATH = Path("outputs/active_z2_sigma/counterterm_immirzi_residual_scalar_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_residual_coefficients_partial.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_coefficients_partial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_coefficients_partial.json")


def build_payload(
    *,
    torsion_path: Path = TORSION_PATH,
    irreducible_path: Path = IRREDUCIBLE_PATH,
    holst_path: Path = HOLST_PATH,
    immirzi_scalar_path: Path = IMMIRZI_SCALAR_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = torsion_path.exists() and irreducible_path.exists() and holst_path.exists()
    output_written = False
    validation_error = None
    coefficients: dict | None = None
    if input_exists:
        try:
            coefficients = build_partial_counterterm_residual_coefficients(
                torsion_pullback_payload=json.loads(torsion_path.read_text(encoding="utf-8")),
                irreducible_torsion_payload=json.loads(irreducible_path.read_text(encoding="utf-8")),
                holst_radial_payload=json.loads(holst_path.read_text(encoding="utf-8")),
                immirzi_scalar_payload=json.loads(immirzi_scalar_path.read_text(encoding="utf-8"))
                if immirzi_scalar_path.exists()
                else None,
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(coefficients, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-residual-coefficients-partial",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {
            "torsion_pullback": str(torsion_path),
            "irreducible_torsion": str(irreducible_path),
            "holst_radial": str(holst_path),
            "immirzi_scalar": str(immirzi_scalar_path),
        },
        "immirzi_scalar_input_exists": immirzi_scalar_path.exists(),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "output_written": output_written,
        "gate_passed": bool(output_written and coefficients and coefficients["R_T_A_ready"]),
        "validation_error": validation_error,
        "coefficients": coefficients or {},
        "next_required": []
        if output_written
        else ["derive active torsion pullback, irreducible torsion, and Holst radial payloads"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    coeff = payload["coefficients"]
    lines = [
        "# Janus Z2/Sigma Counterterm Residual Coefficients Partial",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Output written: `{payload['output_written']}`",
    ]
    if coeff:
        lines.extend(
            [
                f"R_T ready: `{coeff['R_T_A_ready']}`",
                f"R_chi radial contraction ready: `{coeff['R_chi_partial_R_chi_ready']}`",
                f"Full expansion explicit: `{coeff['full_coefficient_expansion_explicit']}`",
                f"Still requires: `{coeff['still_requires']}`",
                f"Still requires for radial contractions: `{coeff['still_requires_for_radial_contractions']}`",
            ]
        )
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

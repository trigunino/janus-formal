from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_inputs import (
    assemble_active_z2sigma_background_scalar_input_manifest,
)


H0_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
CURVATURE_PATH = Path("outputs/active_z2_sigma/background_curvature_inputs.json")
GRAVITY_PATH = Path("outputs/active_z2_sigma/background_gravity_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_scalar_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_scalar_inputs_assembler_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_scalar_inputs_assembler_gate.json")


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(
    *,
    h0_path: Path = H0_PATH,
    curvature_path: Path = CURVATURE_PATH,
    gravity_path: Path = GRAVITY_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    h0_exists = h0_path.exists()
    curvature_exists = curvature_path.exists()
    gravity_exists = gravity_path.exists()
    output_written = False
    validation_error = None
    if h0_exists and curvature_exists and gravity_exists:
        try:
            assembled = assemble_active_z2sigma_background_scalar_input_manifest(
                h0_payload=_read_json(h0_path),
                curvature_payload=_read_json(curvature_path),
                gravity_payload=_read_json(gravity_path),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(assembled, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-background-scalar-inputs-assembler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "h0_input_manifest": str(h0_path),
        "curvature_input_manifest": str(curvature_path),
        "gravity_input_manifest": str(gravity_path),
        "output_manifest": str(output_path),
        "h0_input_exists": h0_exists,
        "curvature_input_exists": curvature_exists,
        "gravity_input_exists": gravity_exists,
        "background_scalar_inputs_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "gate_passed": output_written,
        "primary_blocker": (
            "none"
            if output_written
            else "active_H0_and_R_curv_dimensionful_normalization"
        ),
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_background_H0_inputs_json",
            "supply_outputs_active_z2_sigma_background_curvature_inputs_json",
            "supply_outputs_active_z2_sigma_background_gravity_inputs_json",
            "run_background_scalar_manifest_writer_from_inputs_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Scalar Inputs Assembler Gate",
        "",
        f"H0 input exists: `{payload['h0_input_exists']}`",
        f"Curvature input exists: `{payload['curvature_input_exists']}`",
        f"Gravity input exists: `{payload['gravity_input_exists']}`",
        f"Background scalar inputs written: `{payload['background_scalar_inputs_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

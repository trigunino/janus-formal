from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_inputs import (
    load_active_z2sigma_background_scalar_input_manifest,
)
from janus_lab.z2_sigma_background_manifest import write_active_z2sigma_background_scalar_manifest


INPUT_PATH = Path("outputs/active_z2_sigma/background_scalar_inputs.json")
MANIFEST_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_scalar_manifest_writer_from_inputs_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_scalar_manifest_writer_from_inputs_gate.json")


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    manifest_path: Path = MANIFEST_PATH,
) -> dict:
    input_exists = input_path.exists()
    input_valid = False
    manifest_written = False
    validation_error = None
    if input_exists:
        try:
            payload = load_active_z2sigma_background_scalar_input_manifest(input_path)
            input_valid = True
            scalars = payload["scalars"]
            write_active_z2sigma_background_scalar_manifest(
                manifest_path,
                h0_z2sigma_km_s_mpc=float(scalars["H0_Z2Sigma_km_s_Mpc"]),
                omega_k_z2sigma=float(scalars["omega_k_Z2Sigma"]),
                gravitational_constant_si_z2sigma=float(
                    scalars["gravitational_constant_si_Z2Sigma"]
                ),
                scalar_provenance=payload["scalar_provenance"],
            )
            manifest_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-background-scalar-manifest-writer-from-inputs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(manifest_path),
        "input_exists": input_exists,
        "input_valid": input_valid,
        "manifest_written": manifest_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "gate_passed": manifest_written,
        "primary_blocker": (
            "none"
            if manifest_written
            else "active_background_scalar_inputs_from_H0_Rcurv_G"
        ),
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_background_scalar_inputs_json",
            "run_background_scalar_manifest_gate",
            "run_bao_component_manifest_writer_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Scalar Manifest Writer From Inputs Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Input valid: `{payload['input_valid']}`",
        f"Manifest written: `{payload['manifest_written']}`",
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

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_scale_free_plasma_primitive_input_writer_gate import (
    build_payload as build_plasma_writer_payload,
)
from janus_lab.z2_sigma_active_pipeline import (
    write_scale_free_plasma_primitive_normalization_inputs_from_early_plasma_and_h0_manifests,
)


EARLY_PLASMA_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
H0_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
NORMALIZATION_PATH = Path(
    "outputs/active_z2_sigma/bao_scale_free_plasma_primitive_normalization_inputs.json"
)
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_normalization_input_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_normalization_input_gate.json"
)


def build_payload(
    *,
    early_plasma_path: Path = EARLY_PLASMA_PATH,
    h0_path: Path = H0_PATH,
    normalization_path: Path = NORMALIZATION_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
) -> dict:
    input_exists = {
        "early_plasma": early_plasma_path.exists(),
        "active_h0": h0_path.exists(),
    }
    written = False
    writer_passed = False
    validation_error = None
    if all(input_exists.values()):
        try:
            write_scale_free_plasma_primitive_normalization_inputs_from_early_plasma_and_h0_manifests(
                early_plasma_path,
                h0_path,
                normalization_path,
            )
            written = True
            writer = build_plasma_writer_payload(
                input_path=normalization_path,
                output_path=plasma_primitive_path,
            )
            writer_passed = writer["gate_passed"]
            validation_error = writer["validation_error"]
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-to-scale-free-plasma-primitive-normalization-input-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "normalization_manifest": str(normalization_path),
        "normalization_manifest_written": written,
        "downstream_plasma_writer_passed": writer_passed,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": written and writer_passed,
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_early_plasma_json",
            "supply_outputs_active_z2_sigma_background_H0_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early Plasma To Scale-Free Plasma Primitive Normalization Input Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Normalization manifest written: `{payload['normalization_manifest_written']}`",
        f"Downstream plasma writer passed: `{payload['downstream_plasma_writer_passed']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

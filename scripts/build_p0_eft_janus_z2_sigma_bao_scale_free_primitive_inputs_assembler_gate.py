from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_scale_free_primitive_inputs
from janus_lab.z2_sigma_active_pipeline import (
    write_scale_free_primitive_manifest_from_split_manifests,
)


BACKGROUND_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json")
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_primitive_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_primitive_inputs_assembler_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_primitive_inputs_assembler_gate.json")


def build_payload(
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    required = {
        "background_primitive": {
            "path": str(background_primitive_path),
            "exists": background_primitive_path.exists(),
        },
        "plasma_primitive": {
            "path": str(plasma_primitive_path),
            "exists": plasma_primitive_path.exists(),
        },
    }
    if not all(item["exists"] for item in required.values()):
        return {
            "status": "janus-z2-sigma-bao-scale-free-primitive-inputs-assembler-gate",
            "active_core": "Z2_tunnel_Sigma",
            "required_input_manifests": required,
            "required_input_manifests_available": False,
            "primitive_manifest_written": False,
            "primitive_manifest_valid": False,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_observational_H0_fit": False,
            "gate_passed": False,
            "blocker": "missing active scale-free split primitive manifests",
        }
    written = write_scale_free_primitive_manifest_from_split_manifests(
        background_primitive_path,
        plasma_primitive_path,
        output_path,
    )
    try:
        load_active_z2sigma_scale_free_primitive_inputs(written)
        primitive_manifest_valid = True
    except Exception:
        primitive_manifest_valid = False
    return {
        "status": "janus-z2-sigma-bao-scale-free-primitive-inputs-assembler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "required_input_manifests": required,
        "required_input_manifests_available": True,
        "primitive_manifest": str(written),
        "primitive_manifest_written": True,
        "primitive_manifest_valid": primitive_manifest_valid,
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": primitive_manifest_valid,
        "blocker": None if primitive_manifest_valid else "assembled primitive manifest invalid",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Scale-Free Primitive Inputs Assembler Gate",
        "",
        f"Required inputs available: `{payload['required_input_manifests_available']}`",
        f"Primitive manifest written: `{payload['primitive_manifest_written']}`",
        f"Primitive manifest valid: `{payload['primitive_manifest_valid']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["blocker"]:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from janus_lab.z2_sigma_active_pipeline import (
    write_scale_free_bao_manifest_from_active_component_manifest,
)


COMPONENT_INPUT_PATH = Path("outputs/active_z2_sigma/bao_component_inputs.json")
OUTPUT_MANIFEST_PATH = Path("outputs/active_z2_sigma/bao_scale_free_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_active_manifest_pipeline_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_active_manifest_pipeline_gate.json")


def build_payload(
    component_input_path: Path = COMPONENT_INPUT_PATH,
    output_manifest_path: Path = OUTPUT_MANIFEST_PATH,
) -> dict:
    if not component_input_path.exists():
        return {
            "status": "janus-z2-sigma-bao-scale-free-active-manifest-pipeline-gate",
            "active_core": "Z2_tunnel_Sigma",
            "component_manifest": str(component_input_path),
            "output_manifest": str(output_manifest_path),
            "component_manifest_available": False,
            "pipeline_executed": False,
            "scale_free_bao_input_manifest_written": False,
            "uses_observational_H0_fit": False,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "gate_passed": False,
            "blocker": "missing active-derived component manifest",
        }

    source_hash = hashlib.sha256(component_input_path.read_bytes()).hexdigest()
    written = write_scale_free_bao_manifest_from_active_component_manifest(
        component_input_path,
        output_manifest_path,
    )
    return {
        "status": "janus-z2-sigma-bao-scale-free-active-manifest-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "component_manifest": str(component_input_path),
        "output_manifest": str(written),
        "component_manifest_available": True,
        "pipeline_executed": True,
        "scale_free_bao_input_manifest_written": True,
        "source_component_manifest_sha256": source_hash,
        "uses_observational_H0_fit": False,
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "gate_passed": True,
        "blocker": None,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Scale-Free Active Manifest Pipeline Gate",
        "",
        f"Component manifest: `{payload['component_manifest']}`",
        f"Output manifest: `{payload['output_manifest']}`",
        f"Pipeline executed: `{payload['pipeline_executed']}`",
        f"Scale-free BAO input manifest written: `{payload['scale_free_bao_input_manifest_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload.get("source_component_manifest_sha256"):
        lines.append(f"Source component manifest sha256: `{payload['source_component_manifest_sha256']}`")
    if payload["blocker"]:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

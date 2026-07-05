from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import (
    load_active_z2sigma_scale_free_background_primitive_inputs,
    load_active_z2sigma_scale_free_plasma_primitive_inputs,
)
from janus_lab.z2_sigma_active_pipeline import (
    write_scale_free_split_primitive_manifests_from_active_component_manifest,
)


COMPONENT_MANIFEST_PATH = Path("outputs/active_z2_sigma/bao_component_inputs.json")
BACKGROUND_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json")
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_to_scale_free_split_primitives_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_to_scale_free_split_primitives_gate.json")


def build_payload(
    component_manifest_path: Path = COMPONENT_MANIFEST_PATH,
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
) -> dict:
    if not component_manifest_path.exists():
        return {
            "status": "janus-z2-sigma-bao-component-to-scale-free-split-primitives-gate",
            "active_core": "Z2_tunnel_Sigma",
            "component_manifest": str(component_manifest_path),
            "component_manifest_available": False,
            "background_primitive_written": False,
            "plasma_primitive_written": False,
            "background_primitive_valid": False,
            "plasma_primitive_valid": False,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_observational_H0_fit": False,
            "gate_passed": False,
            "blocker": "missing active BAO component manifest",
        }

    background_path, plasma_path = write_scale_free_split_primitive_manifests_from_active_component_manifest(
        component_manifest_path,
        background_primitive_path,
        plasma_primitive_path,
    )
    background = load_active_z2sigma_scale_free_background_primitive_inputs(background_path)
    plasma = load_active_z2sigma_scale_free_plasma_primitive_inputs(plasma_path)
    grids_aligned = (
        len(background.z_grid) == len(plasma.z_grid)
        and float(background.z_max) == float(plasma.z_max)
    )
    return {
        "status": "janus-z2-sigma-bao-component-to-scale-free-split-primitives-gate",
        "active_core": "Z2_tunnel_Sigma",
        "component_manifest": str(component_manifest_path),
        "component_manifest_available": True,
        "background_primitive_manifest": str(background_path),
        "plasma_primitive_manifest": str(plasma_path),
        "background_primitive_written": True,
        "plasma_primitive_written": True,
        "background_primitive_valid": True,
        "plasma_primitive_valid": True,
        "split_primitive_grids_aligned": grids_aligned,
        "z_grid_length": int(len(background.z_grid)),
        "z_max": float(background.z_max),
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": bool(grids_aligned),
        "blocker": None if grids_aligned else "split primitive grids are not aligned",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Component To Scale-Free Split Primitives Gate",
        "",
        f"Component manifest available: `{payload['component_manifest_available']}`",
        f"Background primitive written: `{payload['background_primitive_written']}`",
        f"Plasma primitive written: `{payload['plasma_primitive_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["blocker"]:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

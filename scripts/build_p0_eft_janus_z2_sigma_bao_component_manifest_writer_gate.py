from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_component_manifest import (
    write_active_z2sigma_bao_component_manifest_from_background_flrw_component_and_early_plasma_manifests,
)


BACKGROUND_SCALAR_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
FLRW_COMPONENT_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
EARLY_PLASMA_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
COMPONENT_MANIFEST_PATH = Path("outputs/active_z2_sigma/bao_component_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_manifest_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_manifest_writer_gate.json")


def _path_status(path: Path) -> dict:
    return {"path": str(path), "exists": path.exists()}


def build_payload(
    *,
    background_scalar_path: Path = BACKGROUND_SCALAR_PATH,
    flrw_component_path: Path = FLRW_COMPONENT_PATH,
    early_plasma_path: Path = EARLY_PLASMA_PATH,
    component_manifest_path: Path = COMPONENT_MANIFEST_PATH,
    z_max: float = 1.0e5,
) -> dict:
    inputs = {
        "background_scalar_manifest": _path_status(background_scalar_path),
        "flrw_component_manifest": _path_status(flrw_component_path),
        "early_plasma_manifest": _path_status(early_plasma_path),
    }
    required_manifests_available = all(item["exists"] for item in inputs.values())
    official_component_manifest_written = False
    validation_error = None
    if required_manifests_available:
        try:
            write_active_z2sigma_bao_component_manifest_from_background_flrw_component_and_early_plasma_manifests(
                component_manifest_path,
                background_scalar_manifest_path=background_scalar_path,
                flrw_component_manifest_path=flrw_component_path,
                early_plasma_manifest_path=early_plasma_path,
                z_max=z_max,
            )
            official_component_manifest_written = True
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-bao-component-manifest-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "background_scalar_manifest": str(background_scalar_path),
        "flrw_component_manifest": str(flrw_component_path),
        "early_plasma_manifest": str(early_plasma_path),
        "component_manifest": str(component_manifest_path),
        "required_manifests": inputs,
        "required_manifests_available": required_manifests_available,
        "strict_component_manifest_writer_ready": True,
        "writer_requires_all_active_component_functions": True,
        "writer_requires_component_provenance": True,
        "writer_rejects_forbidden_provenance_tokens": True,
        "writer_sets_compressed_planck_lcdm_rd_used_false": True,
        "writer_sets_archived_z4_reuse_used_false": True,
        "writer_sets_phenomenological_holst_bao_scan_used_false": True,
        "writer_produces_official_pipeline_compatible_schema": True,
        "official_component_manifest_written": official_component_manifest_written,
        "validation_error": validation_error,
        "gate_passed": official_component_manifest_written,
        "next_required": [
            "write_active_background_scalar_manifest",
            "write_active_FLRW_component_manifest",
            "write_active_early_plasma_manifest",
            "run_active_manifest_pipeline_gate_after_component_manifest_exists",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Component Manifest Writer Gate",
        "",
        f"Writer ready: `{payload['strict_component_manifest_writer_ready']}`",
        f"Required manifests available: `{payload['required_manifests_available']}`",
        f"Official component manifest written: `{payload['official_component_manifest_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Required Manifests",
    ]
    lines.extend(
        f"- `{name}`: `{status['path']}` exists=`{status['exists']}`"
        for name, status in payload["required_manifests"].items()
    )
    if payload.get("validation_error"):
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend([
        "",
        "## Next Required",
    ])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

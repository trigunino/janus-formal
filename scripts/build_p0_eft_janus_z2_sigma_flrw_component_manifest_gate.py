from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_flrw_component_manifest import load_active_z2sigma_flrw_component_manifest


MANIFEST_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_component_manifest_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_component_manifest_gate.json")


def build_payload(*, manifest_path: Path = MANIFEST_PATH) -> dict:
    manifest_exists = manifest_path.exists()
    validation_error = None
    values_ready = False
    if manifest_exists:
        try:
            load_active_z2sigma_flrw_component_manifest(manifest_path)
            values_ready = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-flrw-component-manifest-gate",
        "active_core": "Z2_tunnel_Sigma",
        "manifest_path": str(manifest_path),
        "manifest_exists": manifest_exists,
        "manifest_valid": values_ready,
        "validation_error": validation_error,
        "writer_ready": True,
        "loader_validation_ready": True,
        "merge_into_bao_component_manifest_ready": True,
        "accepted_fields": [
            "cartan_ghy_rho",
            "cartan_ghy_p",
            "holst_nieh_yan_rho",
            "holst_nieh_yan_p",
            "matter_flux_rho",
            "matter_flux_p",
            "counterterm_rho",
            "counterterm_p",
        ],
        "requires_active_provenance": True,
        "compressed_planck_lcdm_background_forbidden": True,
        "archived_z4_reuse_forbidden": True,
        "phenomenological_holst_bao_scan_forbidden": True,
        "flrw_component_values_ready": values_ready,
        "gate_passed": values_ready,
        "next_required": [
            "feed_active_FLRW_stress_component_arrays_to_writer",
            "merge_background_FLRW_and_early_plasma_manifests_into_active_BAO_component_manifest",
            "run_active_BAO_component_to_chi2_pipeline_after_all_values_are_active",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Component Manifest Gate",
        "",
        f"Writer ready: `{payload['writer_ready']}`",
        f"Loader validation ready: `{payload['loader_validation_ready']}`",
        f"BAO component merge ready: `{payload['merge_into_bao_component_manifest_ready']}`",
        f"Manifest: `{payload['manifest_path']}`",
        f"Manifest exists: `{payload['manifest_exists']}`",
        f"Manifest valid: `{payload['manifest_valid']}`",
        f"FLRW component values ready: `{payload['flrw_component_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Accepted Fields",
    ]
    lines.extend(f"- `{item}`" for item in payload["accepted_fields"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_early_plasma_manifest import load_active_z2sigma_early_plasma_manifest


MANIFEST_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_component_manifest_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_component_manifest_gate.json")


def build_payload() -> dict:
    manifest_exists = MANIFEST_PATH.exists()
    validation_error = None
    values_ready = False
    if manifest_exists:
        try:
            load_active_z2sigma_early_plasma_manifest(MANIFEST_PATH)
            values_ready = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-component-manifest-gate",
        "active_core": "Z2_tunnel_Sigma",
        "manifest_path": str(MANIFEST_PATH),
        "manifest_exists": manifest_exists,
        "manifest_valid": values_ready,
        "validation_error": validation_error,
        "writer_ready": True,
        "loader_validation_ready": True,
        "merge_into_bao_component_manifest_ready": True,
        "accepted_fields": [
            "rho_baryon_Z2Sigma",
            "rho_photon_Z2Sigma",
            "Gamma_drag_Z2Sigma",
        ],
        "z_d_bracket_policy": "optional; active BAO pipeline may derive bracket from Gamma_drag-H on z_grid",
        "requires_active_provenance": True,
        "compressed_planck_lcdm_rd_forbidden": True,
        "archived_z4_reuse_forbidden": True,
        "phenomenological_holst_bao_scan_forbidden": True,
        "early_plasma_values_ready": values_ready,
        "gate_passed": values_ready,
        "next_required": [
            "feed_active_baryon_photon_and_Gamma_drag_functions_to_writer",
            "merge_validated_early_plasma_payload_into_active_BAO_component_manifest",
            "solve_z_d_with_active_H_Z2Sigma_in_active_pipeline",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early-Plasma Component Manifest Gate",
        "",
        f"Writer ready: `{payload['writer_ready']}`",
        f"Loader validation ready: `{payload['loader_validation_ready']}`",
        f"BAO component merge ready: `{payload['merge_into_bao_component_manifest_ready']}`",
        f"Manifest: `{payload['manifest_path']}`",
        f"Manifest exists: `{payload['manifest_exists']}`",
        f"Manifest valid: `{payload['manifest_valid']}`",
        f"Early-plasma values ready: `{payload['early_plasma_values_ready']}`",
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

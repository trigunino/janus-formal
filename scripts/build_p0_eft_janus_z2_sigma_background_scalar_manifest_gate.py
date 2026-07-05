from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_manifest import load_active_z2sigma_background_scalar_manifest


MANIFEST_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_scalar_manifest_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_scalar_manifest_gate.json")


def build_payload() -> dict:
    manifest_exists = MANIFEST_PATH.exists()
    validation_error = None
    values_ready = False
    if manifest_exists:
        try:
            load_active_z2sigma_background_scalar_manifest(MANIFEST_PATH)
            values_ready = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-background-scalar-manifest-gate",
        "active_core": "Z2_tunnel_Sigma",
        "manifest_path": str(MANIFEST_PATH),
        "manifest_exists": manifest_exists,
        "manifest_valid": values_ready,
        "validation_error": validation_error,
        "writer_ready": True,
        "loader_validation_ready": True,
        "accepted_fields": [
            "H0_Z2Sigma_km_s_Mpc",
            "omega_k_Z2Sigma",
            "gravitational_constant_si_Z2Sigma",
            "critical_normalization",
        ],
        "requires_active_provenance": True,
        "compressed_planck_lcdm_background_forbidden": True,
        "archived_z4_background_reuse_forbidden": True,
        "observational_H0_fit_forbidden": True,
        "background_scalar_values_ready": values_ready,
        "gate_passed": values_ready,
        "next_required": [
            "feed_active_H0_omega_k_and_G_convention_to_writer",
            "merge_validated_background_scalars_into_active_BAO_component_manifest",
            "feed_active_rho_eff_to_existing_H_Z2Sigma_builder",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Scalar Manifest Gate",
        "",
        f"Writer ready: `{payload['writer_ready']}`",
        f"Loader validation ready: `{payload['loader_validation_ready']}`",
        f"Manifest: `{payload['manifest_path']}`",
        f"Manifest exists: `{payload['manifest_exists']}`",
        f"Manifest valid: `{payload['manifest_valid']}`",
        f"Background scalar values ready: `{payload['background_scalar_values_ready']}`",
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

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_manifest import load_active_z2sigma_background_scalar_manifest


BACKGROUND_SCALAR_MANIFEST_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_critical_normalization_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_critical_normalization_builder_gate.json")


def build_payload() -> dict:
    manifest_exists = BACKGROUND_SCALAR_MANIFEST_PATH.exists()
    manifest_valid = False
    validation_error = None
    if manifest_exists:
        try:
            load_active_z2sigma_background_scalar_manifest(BACKGROUND_SCALAR_MANIFEST_PATH)
            manifest_valid = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-critical-normalization-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "background_scalar_manifest_status": {
            "path": str(BACKGROUND_SCALAR_MANIFEST_PATH),
            "exists": manifest_exists,
            "valid": manifest_valid,
            "validation_error": validation_error,
        },
        "critical_normalization_builder_ready": True,
        "outputs": ["rho_crit0_Z2Sigma", "kappa_Z2Sigma", "kappa_rho_crit0_Z2Sigma"],
        "requires_active_H0_Z2Sigma": True,
        "requires_explicit_gravitational_constant": True,
        "uses_planck_lcdm_H0": False,
        "uses_archived_z4_inputs": False,
        "critical_normalization_values_ready": manifest_valid,
        "gate_passed": manifest_valid,
        "next_required": [
            "derive_active_H0_Z2Sigma",
            "derive_or_declare_active_low_energy_G_Z2Sigma_convention",
            "feed_kappa_rho_crit0_to_Cartan_GHY_component_builder",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Critical Normalization Builder Gate",
        "",
        f"Builder ready: `{payload['critical_normalization_builder_ready']}`",
        f"Values ready: `{payload['critical_normalization_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

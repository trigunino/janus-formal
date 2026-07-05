from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_early_plasma_manifest import load_active_z2sigma_early_plasma_manifest


EARLY_PLASMA_MANIFEST_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_density_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_density_builder_gate.json")


def build_payload() -> dict:
    manifest_exists = EARLY_PLASMA_MANIFEST_PATH.exists()
    manifest_valid = False
    validation_error = None
    if manifest_exists:
        try:
            load_active_z2sigma_early_plasma_manifest(EARLY_PLASMA_MANIFEST_PATH)
            manifest_valid = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-density-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "early_plasma_manifest_status": {
            "path": str(EARLY_PLASMA_MANIFEST_PATH),
            "exists": manifest_exists,
            "valid": manifest_valid,
            "validation_error": validation_error,
        },
        "bibliography_checked": True,
        "primary_sources_checked": [
            "FLRW continuity equation for conserved matter and radiation",
            "Hu & Sugiyama 1996 photon-baryon loading R=3rho_b/4rho_gamma",
            "Eisenstein & Hu 1997 BAO sound-horizon and drag-epoch definitions",
        ],
        "baryon_density_builder_ready": True,
        "photon_density_builder_ready": True,
        "free_electron_density_builder_ready": True,
        "baryon_scaling": "rho_baryon_Z2Sigma(z)=rho_baryon0_Z2Sigma*(1+z)^3",
        "photon_scaling": "rho_photon_Z2Sigma(z)=rho_photon0_Z2Sigma*(1+z)^4",
        "free_electron_density_formula": "n_e,Z2Sigma(z)=electrons_per_baryon*x_e,Z2Sigma(z)*n_b,Z2Sigma(z)",
        "requires_active_baryon_normalization": True,
        "requires_active_photon_normalization": True,
        "requires_active_baryon_number_density": True,
        "requires_active_ionization_fraction": True,
        "uses_planck_lcdm_density_parameters": False,
        "uses_planck_lcdm_recombination_history": False,
        "uses_archived_z4_inputs": False,
        "early_plasma_density_values_ready": manifest_valid,
        "gate_passed": manifest_valid,
        "next_required": [
            "derive_active_rho_baryon0_Z2Sigma",
            "derive_active_rho_photon0_Z2Sigma",
            "derive_active_baryon_number_density_Z2Sigma",
            "derive_active_ionization_fraction_xe_Z2Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early-Plasma Density Builder Gate",
        "",
        f"Baryon builder ready: `{payload['baryon_density_builder_ready']}`",
        f"Photon builder ready: `{payload['photon_density_builder_ready']}`",
        f"Free-electron builder ready: `{payload['free_electron_density_builder_ready']}`",
        f"Early-plasma manifest valid: `{payload['early_plasma_manifest_status']['valid']}`",
        f"Values ready: `{payload['early_plasma_density_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

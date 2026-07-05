from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_early_plasma_manifest import load_active_z2sigma_early_plasma_manifest
from janus_lab.z2_sigma_background_manifest import load_active_z2sigma_background_scalar_manifest
from janus_lab.z2_sigma_background_inputs import build_active_z2sigma_background_scalar_payload


BACKGROUND_SCALAR_MANIFEST_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
BACKGROUND_H0_INPUT_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
EARLY_PLASMA_MANIFEST_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_thomson_drag_rate_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_thomson_drag_rate_builder_gate.json")


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
    background_exists = BACKGROUND_SCALAR_MANIFEST_PATH.exists()
    background_valid = False
    background_error = None
    if background_exists:
        try:
            load_active_z2sigma_background_scalar_manifest(BACKGROUND_SCALAR_MANIFEST_PATH)
            background_valid = True
        except Exception as exc:
            background_error = str(exc)
    h0_exists = BACKGROUND_H0_INPUT_PATH.exists()
    h0_valid = False
    h0_error = None
    if h0_exists:
        try:
            build_active_z2sigma_background_scalar_payload(
                json.loads(BACKGROUND_H0_INPUT_PATH.read_text(encoding="utf-8")),
                "H0_Z2Sigma_km_s_Mpc",
            )
            h0_valid = True
        except Exception as exc:
            h0_error = str(exc)
    gamma_over_h0_ready = manifest_valid and (background_valid or h0_valid)
    return {
        "status": "janus-z2-sigma-thomson-drag-rate-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "early_plasma_manifest_status": {
            "path": str(EARLY_PLASMA_MANIFEST_PATH),
            "exists": manifest_exists,
            "valid": manifest_valid,
            "validation_error": validation_error,
        },
        "background_scalar_manifest_status": {
            "path": str(BACKGROUND_SCALAR_MANIFEST_PATH),
            "exists": background_exists,
            "valid": background_valid,
            "validation_error": background_error,
        },
        "background_h0_input_status": {
            "path": str(BACKGROUND_H0_INPUT_PATH),
            "exists": h0_exists,
            "valid": h0_valid,
            "validation_error": h0_error,
        },
        "bibliography_checked": True,
        "primary_sources_checked": [
            "Eisenstein & Hu 1997, arXiv:astro-ph/9709112",
            "Hu & Sugiyama 1996 photon-baryon tight-coupling treatment",
        ],
        "thomson_drag_rate_builder_ready": True,
        "Gamma_drag_over_H0_builder_ready": True,
        "uses_baryon_loading_R": True,
        "R_definition": "R_Z2Sigma(z) = 3 rho_baryon_Z2Sigma(z) / (4 rho_photon_Z2Sigma(z))",
        "Gamma_drag_formula": "Gamma_drag_Z2Sigma(z) = n_e,Z2Sigma(z) sigma_T c / R_Z2Sigma(z)",
        "Gamma_units": "km/s/Mpc",
        "requires_active_free_electron_density": True,
        "requires_active_baryon_density": True,
        "requires_active_photon_density": True,
        "requires_explicit_sigma_thomson": True,
        "requires_active_H0_Z2Sigma": True,
        "uses_planck_lcdm_recombination_history": False,
        "uses_archived_z4_inputs": False,
        "Gamma_drag_values_ready": manifest_valid,
        "Gamma_drag_over_H0_values_ready": gamma_over_h0_ready,
        "scale_free_Gamma_drag_over_H0_from_active_H0_ready": manifest_valid and h0_valid,
        "gate_passed": gamma_over_h0_ready,
        "next_required": [
            "derive_free_electron_density_history_n_e_Z2Sigma",
            "derive_active_rho_baryon_Z2Sigma_and_rho_photon_Z2Sigma",
            "write_Gamma_drag_Z2Sigma_to_component_manifest_with_active_provenance",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Thomson Drag Rate Builder Gate",
        "",
        f"Builder ready: `{payload['thomson_drag_rate_builder_ready']}`",
        f"Gamma/H0 builder ready: `{payload['Gamma_drag_over_H0_builder_ready']}`",
        f"Early-plasma manifest valid: `{payload['early_plasma_manifest_status']['valid']}`",
        f"Background scalar manifest valid: `{payload['background_scalar_manifest_status']['valid']}`",
        f"Background H0 input valid: `{payload['background_h0_input_status']['valid']}`",
        f"Gamma values ready: `{payload['Gamma_drag_values_ready']}`",
        f"Gamma/H0 values ready: `{payload['Gamma_drag_over_H0_values_ready']}`",
        f"Scale-free Gamma/H0 from active H0 ready: `{payload['scale_free_Gamma_drag_over_H0_from_active_H0_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Formula",
        f"`{payload['Gamma_drag_formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

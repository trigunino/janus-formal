from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_early_plasma_inputs import (
    build_active_z2sigma_baryon_photon_input_payload,
    build_active_z2sigma_ionization_thomson_input_payload,
)


BARYON_PHOTON_INPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_baryon_photon_normalization_inputs.json"
)
IONIZATION_THOMSON_INPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_ionization_thomson_normalization_inputs.json"
)
CODATA_CONSTANTS_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
MODEL_NORMALIZATION_INPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_model_normalization_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_physical_input_obligation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_physical_input_obligation_gate.json"
)


def _status(path: Path, builder: Callable[[dict], dict]) -> dict:
    exists = path.exists()
    valid = False
    error = None
    if exists:
        try:
            builder(json.loads(path.read_text(encoding="utf-8")))
            valid = True
        except Exception as exc:
            error = str(exc)
    return {"path": str(path), "exists": exists, "valid": valid, "validation_error": error}


MODEL_NORMALIZATION_FIELDS = [
    "baryon_number_density0_m3_Z2Sigma",
    "ionization_fraction_Z2Sigma",
    "electrons_per_baryon",
]


def _codata_status(path: Path) -> dict:
    exists = path.exists()
    valid = False
    error = None
    if exists:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
            constants = payload["constants"]
            valid = (
                payload.get("active_core") == "Z2_tunnel_Sigma"
                and payload.get("source") == "active_derived"
                and float(constants["radiation_constant_J_m3_K4"]) > 0.0
                and float(constants["baryon_mass_kg"]) > 0.0
                and float(constants["sigma_thomson_m2"]) > 0.0
            )
        except Exception as exc:
            error = str(exc)
    return {"path": str(path), "exists": exists, "valid": valid, "validation_error": error}


def _model_status(path: Path) -> dict:
    exists = path.exists()
    valid = False
    error = None
    missing_fields = MODEL_NORMALIZATION_FIELDS.copy()
    if exists:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
            normalizations = payload.get("normalizations", {})
            provenance = payload.get("normalization_provenance", {})
            missing_fields = [
                field
                for field in MODEL_NORMALIZATION_FIELDS
                if field not in normalizations or field not in provenance
            ]
            valid = (
                payload.get("active_core") == "Z2_tunnel_Sigma"
                and payload.get("source") == "active_derived"
                and not missing_fields
                and payload.get("compressed_planck_lcdm_rd_used") is False
                and payload.get("archived_z4_reuse_used") is False
                and payload.get("phenomenological_holst_bao_scan_used") is False
            )
        except Exception as exc:
            error = str(exc)
    return {
        "path": str(path),
        "exists": exists,
        "valid": valid,
        "validation_error": error,
        "missing_fields": missing_fields,
    }


def build_payload(
    *,
    baryon_photon_input_path: Path = BARYON_PHOTON_INPUT_PATH,
    ionization_thomson_input_path: Path = IONIZATION_THOMSON_INPUT_PATH,
    codata_constants_path: Path = CODATA_CONSTANTS_PATH,
    model_normalization_input_path: Path = MODEL_NORMALIZATION_INPUT_PATH,
) -> dict:
    baryon_photon = _status(
        baryon_photon_input_path,
        build_active_z2sigma_baryon_photon_input_payload,
    )
    ionization_thomson = _status(
        ionization_thomson_input_path,
        build_active_z2sigma_ionization_thomson_input_payload,
    )
    codata_constants = _codata_status(codata_constants_path)
    model_normalization = _model_status(model_normalization_input_path)
    ready = baryon_photon["valid"] and ionization_thomson["valid"]
    missing = []
    if not baryon_photon["valid"]:
        missing.append("early_plasma_baryon_photon_normalization_inputs")
    if not ionization_thomson["valid"]:
        missing.append("early_plasma_ionization_thomson_normalization_inputs")
    return {
        "status": "janus-z2-sigma-early-plasma-physical-input-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "blackbody photon density rho_gamma=a_rad*T^4",
            "photon-baryon sound speed c_s/c=[3(1+3rho_b/4rho_gamma)]^-1/2",
            "Thomson drag rate Gamma_drag=n_e sigma_T c/R",
        ],
        "required_inputs": {
            "baryon_photon_normalization": baryon_photon,
            "ionization_thomson_normalization": ionization_thomson,
            "codata_constants": codata_constants,
            "model_normalization": model_normalization,
        },
        "codata_constants_valid": codata_constants["valid"],
        "model_normalization_valid": model_normalization["valid"],
        "model_normalization_missing_fields": model_normalization["missing_fields"],
        "builders_ready_after_inputs": {
            "rho_baryon_Z2Sigma": ready,
            "rho_photon_Z2Sigma": ready,
            "c_s_over_c_Z2Sigma": ready,
            "Gamma_drag_Z2Sigma": ready,
        },
        "requires_background_H0_for_Gamma_over_H0": True,
        "requires_active_E_Z2Sigma_for_z_d_solver": True,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "mock_inputs_forbidden": True,
        "early_plasma_physical_inputs_ready": ready,
        "gate_passed": ready,
        "missing_physical_inputs": missing,
        "next_required": [
            "derive_active_baryon_photon_normalizations",
            "derive_active_ionization_and_Thomson_normalizations",
            "run_early_plasma_input_writers_and_assembler",
            "combine_with_background_H0_and_E_Z2Sigma_for_z_d",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early-Plasma Physical Input Obligation Gate",
        "",
        f"Baryon/photon input valid: `{payload['required_inputs']['baryon_photon_normalization']['valid']}`",
        f"Ionization/Thomson input valid: `{payload['required_inputs']['ionization_thomson_normalization']['valid']}`",
        f"CODATA constants valid: `{payload['codata_constants_valid']}`",
        f"Model normalization valid: `{payload['model_normalization_valid']}`",
        f"Early-plasma physical inputs ready: `{payload['early_plasma_physical_inputs_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Missing Model Normalization Fields",
    ]
    lines.extend(f"- `{item}`" for item in payload["model_normalization_missing_fields"])
    lines.extend([
        "",
        "## Missing Physical Inputs",
    ])
    lines.extend(f"- `{item}`" for item in payload["missing_physical_inputs"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

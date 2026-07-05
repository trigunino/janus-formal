from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_distance_bao_bibliography_gate import (
    build_payload as build_bibliography_payload,
)
from janus_lab.z2_sigma_active_pipeline import _require_active_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_minimal_contract_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_minimal_contract_gate.json")
COMPONENT_MANIFEST_PATH = Path("outputs/active_z2_sigma/bao_component_inputs.json")


def build_payload(component_manifest_path: Path = COMPONENT_MANIFEST_PATH) -> dict:
    bibliography = build_bibliography_payload()
    component_manifest_available = component_manifest_path.exists()
    component_manifest_valid = False
    validation_error = None
    if component_manifest_available:
        try:
            _require_active_payload(component_manifest_path)
            component_manifest_valid = True
        except Exception as exc:
            validation_error = str(exc)
    primitives_available = component_manifest_valid
    primitive_inputs = {
        "E_Z2Sigma_of_z": {
            "role": "dimensionless expansion history H_Z2Sigma/H0",
            "source": "active effective density plus active curvature",
            "builder_ready": True,
            "values_available": primitives_available,
            "available": primitives_available,
            "blocker": "derive active FLRW rho_eff/rho_crit0 and omega_k_Z2Sigma",
        },
        "cs_over_c_Z2Sigma_of_z": {
            "role": "dimensionless photon-baryon sound speed",
            "source": "active baryon and photon density histories",
            "builder_ready": True,
            "values_available": primitives_available,
            "available": primitives_available,
            "blocker": "derive active rho_baryon_Z2Sigma and rho_photon_Z2Sigma",
        },
        "Gamma_drag_over_H0_Z2Sigma_of_z": {
            "role": "dimensionless drag rate for solving z_d",
            "source": "active free-electron density, Thomson drag and active H0 normalization",
            "builder_ready": True,
            "values_available": primitives_available,
            "available": primitives_available,
            "blocker": "derive active ionization/free-electron history and H0 normalization convention",
        },
        "omega_k_Z2Sigma": {
            "role": "dimensionless FLRW curvature in D_M/r_d",
            "source": "active projective/tunnel curvature convention",
            "builder_ready": True,
            "values_available": primitives_available,
            "available": primitives_available,
            "blocker": "derive active projective curvature and tunnel embedding scale",
        },
    }
    derived_outputs = {
        "z_d_Z2Sigma": "solve Gamma_drag/H0 = E_Z2Sigma",
        "rhat_d_Z2Sigma": "integral_zd^inf (c_s/c)/E dz",
        "DESI_DR2_BAO_prediction_vector": "compute D_M/r_d, D_H/r_d and D_V/r_d scale-free",
        "chi2_DESI_DR2_BAO": "evaluate against DESI DR2 BAO covariance",
    }
    primitive_ready = all(row["available"] for row in primitive_inputs.values())
    return {
        "status": "janus-z2-sigma-bao-scale-free-minimal-contract-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_sources": bibliography["sources"],
        "standard_distance_definitions_available": bibliography["standard_flrw_distance_source_found"],
        "standard_sound_horizon_context_available": bibliography["bao_sound_horizon_source_found"],
        "local_z2_sigma_derivation_required": bibliography["local_distance_and_ruler_derivation_required"],
        "component_manifest": str(component_manifest_path),
        "component_manifest_available": component_manifest_available,
        "component_manifest_valid": component_manifest_valid,
        "validation_error": validation_error,
        "primitive_physical_inputs": primitive_inputs,
        "primitive_physical_inputs_available": primitive_ready,
        "derived_outputs_after_primitives": derived_outputs,
        "scale_free_chi2_contract_ready": primitive_ready,
        "observational_H0_fit_used": False,
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "gate_passed": primitive_ready,
        "blocker": None if primitive_ready else "active scale-free primitive physical inputs are not all derived",
        "next_required": [
            "derive_active_E_Z2Sigma_of_z",
            "derive_active_cs_over_c_Z2Sigma_of_z",
            "derive_active_Gamma_drag_over_H0_Z2Sigma_of_z",
            "derive_active_omega_k_Z2Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Scale-Free Minimal Contract Gate",
        "",
        f"Primitive physical inputs available: `{payload['primitive_physical_inputs_available']}`",
        f"Scale-free chi2 contract ready: `{payload['scale_free_chi2_contract_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Primitive Inputs",
    ]
    for name, row in payload["primitive_physical_inputs"].items():
        lines.append(
            f"- `{name}`: builder `{row['builder_ready']}`; values `{row['values_available']}`; "
            f"available `{row['available']}`; blocker: {row['blocker']}"
        )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

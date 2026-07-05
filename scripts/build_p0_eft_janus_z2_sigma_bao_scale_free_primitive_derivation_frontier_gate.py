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
from scripts.build_p0_eft_janus_z2_sigma_distance_bao_bibliography_gate import (
    build_payload as build_bibliography_payload,
)


BACKGROUND_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json")
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_primitive_derivation_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_primitive_derivation_frontier_gate.json")


DERIVATION_OBLIGATIONS = {
    "E_Z2Sigma": {
        "target_manifest": str(BACKGROUND_PRIMITIVE_PATH),
        "required_from": [
            "active effective fluid rho_eff/rho_crit0",
            "active H0 normalization convention",
            "active FLRW curvature branch",
        ],
    },
    "omega_k_Z2Sigma": {
        "target_manifest": str(BACKGROUND_PRIMITIVE_PATH),
        "required_from": [
            "projective S4->RP4 cover geometry",
            "resolved tunnel Sigma curvature radius/sign convention",
            "active FLRW spatial metric branch",
        ],
    },
    "c_s_over_c_Z2Sigma": {
        "target_manifest": str(PLASMA_PRIMITIVE_PATH),
        "required_from": [
            "active baryon density history",
            "active photon density history",
            "photon-baryon tight-coupling sound-speed formula",
        ],
    },
    "Gamma_drag_over_H0_Z2Sigma": {
        "target_manifest": str(PLASMA_PRIMITIVE_PATH),
        "required_from": [
            "active ionization/free-electron history",
            "Thomson drag rate",
            "active H0 normalization convention",
        ],
    },
}


def _manifest_status(path: Path, loader) -> dict:
    if not path.exists():
        return {"path": str(path), "exists": False, "valid": False, "error": "missing manifest"}
    try:
        loaded = loader(path)
    except Exception as exc:
        return {"path": str(path), "exists": True, "valid": False, "error": str(exc)}
    return {
        "path": str(path),
        "exists": True,
        "valid": True,
        "error": None,
        "z_grid_length": int(len(loaded.z_grid)),
        "z_max": float(loaded.z_max),
    }


def build_payload(
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
) -> dict:
    bibliography = build_bibliography_payload()
    background_status = _manifest_status(
        background_primitive_path,
        load_active_z2sigma_scale_free_background_primitive_inputs,
    )
    plasma_status = _manifest_status(
        plasma_primitive_path,
        load_active_z2sigma_scale_free_plasma_primitive_inputs,
    )
    split_manifests_valid = bool(background_status["valid"] and plasma_status["valid"])
    aligned_z_grid_declared = split_manifests_valid
    if split_manifests_valid:
        aligned_z_grid_declared = (
            background_status["z_grid_length"] == plasma_status["z_grid_length"]
            and background_status["z_max"] == plasma_status["z_max"]
        )
    frontier_closed = bool(split_manifests_valid and aligned_z_grid_declared)
    return {
        "status": "janus-z2-sigma-bao-scale-free-primitive-derivation-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_sources": bibliography["sources"],
        "standard_distance_definitions_available": bibliography["standard_flrw_distance_source_found"],
        "standard_sound_horizon_context_available": bibliography["bao_sound_horizon_source_found"],
        "local_z2_sigma_derivation_required": bibliography["local_distance_and_ruler_derivation_required"],
        "derivation_obligations": DERIVATION_OBLIGATIONS,
        "background_primitive_manifest": background_status,
        "plasma_primitive_manifest": plasma_status,
        "split_primitive_manifests_valid": split_manifests_valid,
        "split_primitive_grids_aligned": aligned_z_grid_declared,
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "phenomenological_holst_bao_scan_used": False,
        "frontier_closed": frontier_closed,
        "gate_passed": frontier_closed,
        "blocker": None
        if frontier_closed
        else "derive and write valid active scale-free background and plasma primitive manifests",
        "next_required": [
            "derive_E_Z2Sigma_and_omega_k_Z2Sigma_into_background_primitive_manifest",
            "derive_c_s_over_c_and_Gamma_drag_over_H0_into_plasma_primitive_manifest",
            "run_bao_scale_free_primitive_inputs_assembler_gate",
            "run_bao_scale_free_primitive_chi2_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Scale-Free Primitive Derivation Frontier Gate",
        "",
        f"Background primitive valid: `{payload['background_primitive_manifest']['valid']}`",
        f"Plasma primitive valid: `{payload['plasma_primitive_manifest']['valid']}`",
        f"Split primitive grids aligned: `{payload['split_primitive_grids_aligned']}`",
        f"Frontier closed: `{payload['frontier_closed']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Derivation Obligations",
    ]
    for name, row in payload["derivation_obligations"].items():
        lines.append(f"- `{name}` -> `{row['target_manifest']}`")
    if payload["blocker"]:
        lines.extend(["", f"Blocker: `{payload['blocker']}`"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

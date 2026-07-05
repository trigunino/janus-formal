from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


TORSION_COMPONENTS_PATH = Path("outputs/active_z2_sigma/flrw_irreducible_torsion_components.json")
A_GRID_PATH = Path("outputs/active_z2_sigma/rsigma_a_grid_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_radial_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_nieh_yan_radial_inputs_from_torsionless_identity_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_nieh_yan_radial_inputs_from_torsionless_identity_gate.json")


def _reject_forbidden(payload: dict) -> None:
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _load_torsion(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("torsion components active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("torsion components source must be active_derived")
    _reject_forbidden(payload)
    for key in [
        "Sigma_torsion_pullback_ready",
        "trace_vector_component_ready",
        "axial_vector_component_ready",
        "tensor_torsion_component_ready",
    ]:
        if payload.get(key) is not True:
            raise ValueError(f"{key} must be true")
    arrays = [
        np.asarray(payload.get("trace_vector_values"), dtype=float),
        np.asarray(payload.get("axial_totally_antisymmetric_component_values"), dtype=float),
        np.asarray(payload.get("tensor_torsion_values"), dtype=float),
    ]
    if any(not np.all(np.isfinite(array)) for array in arrays):
        raise ValueError("torsion irreducible components must be finite")
    max_abs = max(float(np.max(np.abs(array))) if array.size else 0.0 for array in arrays)
    if max_abs > 1e-12:
        raise ValueError("torsionless Nieh-Yan zero identity requires all torsion components to vanish")
    return payload


def _load_grid(path: Path) -> list[float]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("a-grid active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("a-grid source must be active_derived")
    _reject_forbidden(payload)
    grid = np.asarray(payload.get("a_grid"), dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    return grid.tolist()


def build_payload(
    *,
    torsion_components_path: Path = TORSION_COMPONENTS_PATH,
    a_grid_path: Path = A_GRID_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "flrw_irreducible_torsion_components": torsion_components_path.exists(),
        "rsigma_a_grid_inputs": a_grid_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            _load_torsion(torsion_components_path)
            grid = _load_grid(a_grid_path)
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "torsion_pullback_on_Sigma_ready": True,
                "FLRW_irreducible_torsion_pullback_ready": True,
                "Immirzi_radial_profile_ready": False,
                "torsionless_Nieh_Yan_zero_identity_ready": True,
                "holst_nieh_yan_radial_reduction_ready": True,
                "selected_radial_term": "E_HolstNiehYan",
                "a_grid": grid,
                "E_HolstNiehYan_values": [0.0 for _ in grid],
                "holst_nieh_yan_route": "torsionless_Nieh_Yan_zero_identity",
                "torsionless_baseline_only": True,
                "identity": "T=0 -> NY=d(e^a wedge T_a)=0 -> delta_RSigma S_HNY=0 for any Immirzi profile",
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-holst-nieh-yan-radial-inputs-from-torsionless-identity-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "holst_nieh_yan_radial_inputs_from_torsionless_identity_written": output_written,
        "torsionless_baseline_only": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "torsionless_FLRW_components_and_a_grid",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_or_supply_flrw_irreducible_torsion_components",
            "derive_or_supply_rsigma_a_grid_inputs",
            "or_derive_nonzero_Holst_Nieh_Yan_radial_reduction_with_Immirzi_profile",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Holst-Nieh-Yan Radial Inputs From Torsionless Identity Gate",
        "",
        f"Output written: `{payload['holst_nieh_yan_radial_inputs_from_torsionless_identity_written']}`",
        f"Torsionless baseline only: `{payload['torsionless_baseline_only']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

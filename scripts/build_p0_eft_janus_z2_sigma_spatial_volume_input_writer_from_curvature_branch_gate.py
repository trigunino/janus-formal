from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate import (
    build_payload as build_curvature_branch_inputs_assembler_payload,
)


MPC_TO_M = 3.0856775814913673e22
INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/spatial_volume_projective_slice_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_spatial_volume_input_writer_from_curvature_branch_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_spatial_volume_input_writer_from_curvature_branch_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    for token in ["planck", "lcdm", "lambda-cdm", "lambda cdm", "z4", "fit"]:
        if token in lowered:
            raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def _write_volume_input(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Curvature branch active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Curvature branch source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    scalars = payload.get("scalars", {})
    provenance = payload.get("scalar_provenance", {})
    r_mpc = float(scalars["R_curv_Z2Sigma_Mpc"])
    k_value = int(scalars["k_Z2Sigma"])
    if float(scalars["k_Z2Sigma"]) != float(k_value):
        raise ValueError("k_Z2Sigma must be an integer -1, 0 or 1")
    if r_mpc <= 0.0:
        raise ValueError("R_curv_Z2Sigma_Mpc must be positive")
    if k_value != 1:
        raise ValueError("Spatial-volume projective slice writer requires k_Z2Sigma = +1")
    r_provenance = _clean_source(provenance.get("R_curv_Z2Sigma", ""), "R_curv_Z2Sigma")
    k_provenance = _clean_source(provenance.get("k_Z2Sigma", ""), "k_Z2Sigma")
    spatial_topology = payload.get("spatial_topology", {
        "quotient_spatial_slice": "RP3",
    })
    quotient_leaf = spatial_topology.get("quotient_spatial_slice")
    if quotient_leaf not in ["RP3", "S3_paired_leaf_representative"]:
        raise ValueError("quotient_spatial_slice must be RP3 or S3_paired_leaf_representative")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "R_curv_Z2Sigma_m": r_mpc * MPC_TO_M,
            "k_Z2Sigma": k_value,
        },
        "scalar_provenance": {
            "R_curv_Z2Sigma_m": f"converted_Mpc_to_m:({r_provenance})",
            "k_Z2Sigma": k_provenance,
        },
        "spatial_topology": {
            "quotient_spatial_slice": quotient_leaf,
        },
        "conversion_policy": {
            "source_radius_field": "R_curv_Z2Sigma_Mpc",
            "output_radius_field": "R_curv_Z2Sigma_m",
            "Mpc_to_m": MPC_TO_M,
            "requires_positive_closed_spatial_branch": True,
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    branch_assembler = build_curvature_branch_inputs_assembler_payload()
    assembler_inputs = branch_assembler.get("input_manifests", {})
    missing_active_artifacts = [
        path
        for key, path in assembler_inputs.items()
        if key in ["h0", "curvature_radius", "curvature_sign"]
        and not Path(path).exists()
    ]
    output_written = False
    validation_error = None
    radius_m = None
    if input_exists:
        try:
            output = _write_volume_input(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            radius_m = output["scalars"]["R_curv_Z2Sigma_m"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-spatial-volume-input-writer-from-curvature-branch-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "curvature_branch_inputs_assembler_passed": branch_assembler["gate_passed"],
        "input_active_derived_manifest_is_authoritative": True,
        "missing_active_artifacts": missing_active_artifacts,
        "nearest_missing_artifact": (
            str(input_path)
            if not input_exists
            else missing_active_artifacts[0]
            if missing_active_artifacts
            else None
        ),
        "nearest_spatial_volume_input_frontier": {
            "blocks": [] if output_written else [
                "active_curvature_branch_manifest",
                "active_H0_Z2Sigma_scale_normalization",
                "active_R_curv_Z2Sigma_Mpc_from_embedding_or_throat_scale",
                "active_closed_projective_spatial_branch_k_plus_one",
            ],
            "nearest_missing_artifact": (
                str(input_path)
                if not input_exists
                else missing_active_artifacts[0]
                if missing_active_artifacts
                else None
            ),
            "curvature_branch_inputs_assembler_passed": branch_assembler["gate_passed"],
            "dimensionless_H0R_over_c_insufficient_for_physical_volume": True,
            "diagnostic_only": True,
        },
        "dimensionless_H0R_over_c_insufficient_for_physical_volume": True,
        "requires_dimensional_R_curv_not_scale_free_inverse": True,
        "spatial_volume_projective_slice_input_written": output_written,
        "Mpc_to_m_conversion_declared": True,
        "requires_positive_closed_spatial_branch": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "R_curv_Z2Sigma_m_value": radius_m,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_curvature_branch_manifest",
        "validation_error": validation_error,
        "next_required": [
            "derive_active_FLRW_closed_projective_spatial_branch",
            "derive_active_R_curv_Z2Sigma_Mpc_not_from_scale_free_BAO_fit",
            "supply_outputs_active_z2_sigma_background_curvature_branch_inputs_json",
            "run_spatial_volume_projective_slice_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spatial Volume Input Writer From Curvature Branch Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Input written: `{payload['spatial_volume_projective_slice_input_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

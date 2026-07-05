from __future__ import annotations

import json
import math
from pathlib import Path


INPUT_PATH = Path("outputs/active_z2_sigma/spatial_volume_projective_slice_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/spatial_volume_normalization_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate.json"
)


FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_background_reuse_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
]


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _build_volume(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in FORBIDDEN_FLAGS:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")

    scalars = payload.get("scalars", {})
    provenance = payload.get("scalar_provenance", {})
    r_curv = float(scalars["R_curv_Z2Sigma_m"])
    k_value = int(scalars["k_Z2Sigma"])
    if r_curv <= 0.0:
        raise ValueError("R_curv_Z2Sigma_m must be positive")
    if k_value != 1:
        raise ValueError("Finite positive-curvature spatial volume requires k_Z2Sigma = +1")
    if "R_curv_Z2Sigma_m" not in provenance:
        raise ValueError("Missing R_curv_Z2Sigma_m provenance")

    topology = payload.get("spatial_topology", {})
    quotient_leaf = topology.get("quotient_spatial_slice", "RP3")
    if quotient_leaf == "RP3":
        volume_factor = 1.0
        convention = "closed_projective_RP3_spatial_volume"
    elif quotient_leaf == "S3_paired_leaf_representative":
        volume_factor = 2.0
        convention = "closed_paired_leaf_S3_representative_volume"
    else:
        raise ValueError("quotient_spatial_slice must be RP3 or S3_paired_leaf_representative")

    rp3_volume = math.pi**2 * r_curv**3
    s3_volume = 2.0 * math.pi**2 * r_curv**3
    volume0 = volume_factor * math.pi**2 * r_curv**3
    if volume0 <= 0.0:
        raise ValueError("spatial_volume0_m3_Z2Sigma must be positive")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "normalizations": {
            "spatial_volume0_m3_Z2Sigma": volume0,
            "projective_RP3_volume0_m3_Z2Sigma": rp3_volume,
            "paired_leaf_S3_volume0_m3_Z2Sigma": s3_volume,
        },
        "normalization_provenance": {
            "spatial_volume0_m3_Z2Sigma": (
                "derived_from_half_cover_spatial_volume_closed_RP3_specialization"
            ),
            "projective_RP3_volume0_m3_Z2Sigma": provenance["R_curv_Z2Sigma_m"],
            "paired_leaf_S3_volume0_m3_Z2Sigma": provenance["R_curv_Z2Sigma_m"],
        },
        "volume_policy": {
            "volume_convention": convention,
            "selected_spatial_quotient_leaf": quotient_leaf,
            "volume_factor_pi2_R3": volume_factor,
            "general_formula": "V0_Z2Sigma = volume_factor*pi^2*R_curv^3",
            "closed_RP3_specialization": "V0_Z2Sigma = pi^2 R_curv^3",
            "closed_paired_leaf_S3_representative": "V0_Z2Sigma = 2*pi^2 R_curv^3",
            "S3_cover_volume": "2*pi^2*R_curv^3",
            "RP3_projective_volume": "pi^2*R_curv^3",
            "z2_cover_factor_applied_once": quotient_leaf == "RP3",
            "finite_volume_requires_k_Z2Sigma_plus_one": True,
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    volume_value = None
    if input_exists:
        try:
            output = _build_volume(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            volume_value = output["normalizations"]["spatial_volume0_m3_Z2Sigma"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-spatial-volume-projective-slice-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "spatial_volume_normalization_written": output_written,
        "closed_projective_RP3_volume_formula_ready": True,
        "closed_paired_leaf_S3_volume_formula_ready": True,
        "formula": "V0_Z2Sigma = volume_factor*pi^2*R_curv^3; RP3 factor=1, paired-leaf S3 factor=2",
        "requires_k_Z2Sigma_plus_one": True,
        "requires_active_R_curv_Z2Sigma": True,
        "requires_active_cover_spatial_metric_or_closed_RP3_branch": True,
        "z2_cover_factor_applied_once": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "uses_observational_H0_fit": False,
        "spatial_volume0_m3_Z2Sigma_value": volume_value,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_R_curv_Z2Sigma_and_k_plus_one",
        "validation_error": validation_error,
        "next_required": [
            "derive_active_FLRW_closed_projective_spatial_branch",
            "derive_active_R_curv_Z2Sigma_in_meters",
            "derive_curvature_sign_k_Z2Sigma_from_active_metric_or_embedding",
            "write_spatial_volume_projective_slice_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spatial Volume Projective Slice Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Formula ready: `{payload['closed_projective_RP3_volume_formula_ready']}`",
        f"Spatial volume written: `{payload['spatial_volume_normalization_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        f"Formula: `{payload['formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

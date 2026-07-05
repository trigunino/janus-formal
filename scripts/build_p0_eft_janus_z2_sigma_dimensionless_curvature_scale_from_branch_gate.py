from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background import dimensionless_curvature_scale_from_h0_radius
from janus_lab.z2_sigma_background_manifest import FORBIDDEN_PROVENANCE_TOKENS
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate import (
    build_payload as build_curvature_branch_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/background_dimensionless_curvature_scale_normalization_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionless_curvature_scale_from_branch_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionless_curvature_scale_from_branch_gate.json"
)


def _clean_provenance(value: str, field: str) -> str:
    cleaned = str(value).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def _build_output(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Curvature branch payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Curvature branch payload source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")

    scalars = payload.get("scalars", {})
    h0 = float(scalars["H0_Z2Sigma_km_s_Mpc"])
    radius = float(scalars["R_curv_Z2Sigma_Mpc"])
    scale = dimensionless_curvature_scale_from_h0_radius(h0, radius)

    provenance = payload.get("scalar_provenance", {})
    h0_provenance = _clean_provenance(provenance.get("H0_Z2Sigma", ""), "H0_Z2Sigma")
    radius_provenance = _clean_provenance(
        provenance.get("R_curv_Z2Sigma", ""),
        "R_curv_Z2Sigma",
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"h0_R_curv_over_c_Z2Sigma": scale},
        "scalar_provenance": {
            "h0_R_curv_over_c_Z2Sigma": (
                "active_flrw_spatial_metric_branch:"
                f"H0=({h0_provenance});R_curv=({radius_provenance})"
            )
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    branch_passed = input_exists
    if not input_exists:
        branch = build_curvature_branch_payload(output_path=input_path)
        branch_passed = branch["gate_passed"]
        input_exists = input_path.exists()
    output_written = False
    validation_error = None
    scale_value = None
    if input_exists:
        try:
            output = _build_output(json.loads(input_path.read_text(encoding="utf-8")))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            scale_value = output["scalars"]["h0_R_curv_over_c_Z2Sigma"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-dimensionless-curvature-scale-from-branch-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "curvature_branch_assembler_passed": branch_passed,
        "dimensionless_curvature_scale_normalization_written": output_written,
        "h0_R_curv_over_c_value": scale_value,
        "formula": "H0_Z2Sigma*R_curv_Z2Sigma/c",
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_active_FLRW_spatial_metric_branch_values",
            "supply_outputs_active_z2_sigma_background_curvature_branch_inputs_json",
            "run_dimensionless_curvature_scale_input_writer_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dimensionless Curvature Scale From Branch Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Branch assembler passed: `{payload['curvature_branch_assembler_passed']}`",
        f"Normalization written: `{payload['dimensionless_curvature_scale_normalization_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
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

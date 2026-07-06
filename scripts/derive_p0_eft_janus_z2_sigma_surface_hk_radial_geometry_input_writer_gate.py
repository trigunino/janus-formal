from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_surface_hk import reduce_surface_hk_radial_geometry_tensors


INPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_radial_tensor_geometry_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_radial_geometry_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_radial_geometry_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_radial_geometry_input_writer_gate.json"
)


def _load_active(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = _load_active(input_path)
            reduced = reduce_surface_hk_radial_geometry_tensors(
                induced_metric_h_ab=source["induced_metric_h_ab"],
                extrinsic_curvature_K_ab=source["extrinsic_curvature_K_ab"],
                partial_R_induced_metric_h_ab=source["partial_R_induced_metric_h_ab"],
                partial_R_extrinsic_curvature_K_ab=source[
                    "partial_R_extrinsic_curvature_K_ab"
                ],
            )
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "fitted_counterterm_coefficient_used": False,
                "a_grid": source["a_grid"],
                "R_Sigma_values": source["R_Sigma_values"],
            }
            output.update({key: value.tolist() for key, value in reduced.items()})
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-surface-hk-radial-geometry-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "surface_hk_radial_geometry_inputs_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "surface_hk_radial_tensor_geometry_inputs",
        "validation_error": validation_error,
        "required_input_fields": [
            "a_grid",
            "R_Sigma_values",
            "induced_metric_h_ab",
            "extrinsic_curvature_K_ab",
            "partial_R_induced_metric_h_ab",
            "partial_R_extrinsic_curvature_K_ab",
        ],
        "next_required": []
        if output_written
        else [
            "derive_active_h_K_partial_R_h_partial_R_K_tensor_geometry",
            "write_surface_hk_radial_tensor_geometry_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Radial Geometry Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['surface_hk_radial_geometry_inputs_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Required Input Fields"])
    lines.extend(f"- `{field}`" for field in payload["required_input_fields"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

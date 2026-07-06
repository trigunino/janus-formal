from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_surface_hk import riccati_normal_flow_radial_primitives


INPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_normal_flow_geometry_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_radial_tensor_geometry_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_riccati_normal_flow_to_surface_hk_geometry_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_riccati_normal_flow_to_surface_hk_geometry_gate.json"
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
            primitives = riccati_normal_flow_radial_primitives(
                induced_metric_h_ab=source["induced_metric_h_ab"],
                extrinsic_curvature_K_ab=source["extrinsic_curvature_K_ab"],
                normal_riemann_R_nabn=source["normal_riemann_R_nabn"],
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
                "induced_metric_h_ab": source["induced_metric_h_ab"],
                "extrinsic_curvature_K_ab": source["extrinsic_curvature_K_ab"],
                "partial_R_induced_metric_h_ab": primitives[
                    "partial_R_induced_metric_h_ab"
                ].tolist(),
                "partial_R_extrinsic_curvature_K_ab": primitives[
                    "partial_R_extrinsic_curvature_K_ab"
                ].tolist(),
                "normal_flow_formula": "partial_R h_ab=2K_ab; partial_R K_ab=R_nabn+K_a^cK_cb",
                "normal_orientation": source.get("normal_orientation", "declared_in_upstream_geometry"),
                "sign_conventions": source.get("sign_conventions", "surface_hk_variation_convention_gate"),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-riccati-normal-flow-to-surface-hk-geometry-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "riccati_surface_hk_tensor_geometry_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "surface_hk_normal_flow_geometry_inputs",
        "validation_error": validation_error,
        "required_input_fields": [
            "a_grid",
            "R_Sigma_values",
            "induced_metric_h_ab",
            "extrinsic_curvature_K_ab",
            "normal_riemann_R_nabn",
        ],
        "next_required": []
        if output_written
        else [
            "derive_active_induced_metric_h_ab",
            "derive_active_extrinsic_curvature_K_ab",
            "derive_active_normal_riemann_R_nabn",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Riccati Normal Flow To Surface h/K Geometry Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['riccati_surface_hk_tensor_geometry_written']}`",
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

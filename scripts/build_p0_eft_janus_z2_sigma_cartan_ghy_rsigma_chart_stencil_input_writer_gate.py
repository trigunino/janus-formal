from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_cartan_ghy import (
    build_cartan_ghy_rsigma_embedding_stencil_from_chart_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_rsigma_chart_stencil_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_rsigma_embedding_stencil_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_rsigma_chart_stencil_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_rsigma_chart_stencil_input_writer_gate.json"
)


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
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
            source = _load_input(input_path)
            payload = build_cartan_ghy_rsigma_embedding_stencil_from_chart_payload(
                a_grid=source["a_grid"],
                radial_offsets=source["radial_offsets"],
                metric_covariant_stencil=source["metric_covariant_stencil"],
                metric_derivatives_stencil=source["metric_derivatives_stencil"],
                tangent_vectors_stencil=source["tangent_vectors_stencil"],
                second_embedding_stencil=source["second_embedding_stencil"],
                level_gradient_covector_stencil=source["level_gradient_covector_stencil"],
                normal_norm_sign=source["normal_norm_sign"],
                orientation_sign=source["orientation_sign"],
                z2_orientation_sign=source["z2_orientation_sign"],
                kappa_Z2Sigma=source["kappa_Z2Sigma"],
                term_provenance=source["E_CartanGHY_provenance"],
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-cartan-ghy-rsigma-chart-stencil-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "chart_stencil_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "Cartan_GHY_chart_radial_stencil",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_metric_covariant_stencil",
            "derive_metric_derivatives_stencil",
            "derive_tangent_vectors_stencil",
            "derive_second_embedding_stencil",
            "derive_level_gradient_covector_stencil",
            "supply_outputs_active_z2_sigma_cartan_ghy_rsigma_chart_stencil_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY R_Sigma Chart Stencil Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['chart_stencil_written']}`",
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

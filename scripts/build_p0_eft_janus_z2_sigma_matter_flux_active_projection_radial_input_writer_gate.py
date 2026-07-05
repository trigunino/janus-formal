from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_matter_flux import build_active_matter_flux_projection_payload


INPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_projection_components.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_active_projection_radial_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_matter_flux_active_projection_radial_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_matter_flux_active_projection_radial_input_writer_gate.json"
)


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


def _load_source(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("projection components active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("projection components source must be active_derived")
    _reject_forbidden(payload)
    for key in [
        "a_grid",
        "T_plus_munu_values",
        "T_minus_munu_values",
        "tangent_vectors_values",
        "normal_plus_values",
        "normal_minus_values",
        "radial_variation_tangent_weights",
    ]:
        if key not in payload:
            raise ValueError(f"projection components missing {key}")
    return payload


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = _load_source(input_path)
            output = build_active_matter_flux_projection_payload(source)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-matter-flux-active-projection-radial-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "active_projection_radial_input_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_matter_flux_projection_components",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_T_plus_minus_munu_on_Sigma",
            "derive_tangent_vectors_and_unit_normals_on_Sigma",
            "derive_radial_variation_tangent_weights_deltaX_RSigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Active Projection Radial Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['active_projection_radial_input_written']}`",
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

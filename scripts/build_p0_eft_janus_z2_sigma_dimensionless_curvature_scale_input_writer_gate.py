from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_manifest import FORBIDDEN_PROVENANCE_TOKENS


INPUT_PATH = Path("outputs/active_z2_sigma/background_dimensionless_curvature_scale_normalization_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_dimensionless_curvature_scale_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionless_curvature_scale_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionless_curvature_scale_input_writer_gate.json"
)


def _build_output(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    value = float(payload["scalars"]["h0_R_curv_over_c_Z2Sigma"])
    if value <= 0.0:
        raise ValueError("h0_R_curv_over_c_Z2Sigma must be positive")
    provenance = str(
        payload.get("scalar_provenance", {}).get("h0_R_curv_over_c_Z2Sigma", "")
    ).strip()
    if not provenance:
        raise ValueError("Missing h0_R_curv_over_c_Z2Sigma provenance")
    lowered = provenance.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden h0_R_curv_over_c_Z2Sigma provenance: {provenance}")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"h0_R_curv_over_c_Z2Sigma": value},
        "scalar_provenance": {"h0_R_curv_over_c_Z2Sigma": provenance},
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    scale_value = None
    if input_exists:
        try:
            output = _build_output(json.loads(input_path.read_text(encoding="utf-8")))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
            scale_value = output["scalars"]["h0_R_curv_over_c_Z2Sigma"]
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-dimensionless-curvature-scale-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "dimensionless_curvature_scale_input_written": output_written,
        "h0_R_curv_over_c_value": scale_value,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_active_dimensionless_curvature_scale_H0_Rcurv_over_c",
            "supply_outputs_active_z2_sigma_background_dimensionless_curvature_scale_normalization_inputs_json",
            "run_scale_free_omega_k_from_curvature_scale_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dimensionless Curvature Scale Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Dimensionless curvature scale written: `{payload['dimensionless_curvature_scale_input_written']}`",
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

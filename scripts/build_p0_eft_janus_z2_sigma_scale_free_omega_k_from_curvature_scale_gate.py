from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from janus_lab.z2_sigma_background import omega_k_from_dimensionless_curvature_scale


SIGN_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
SCALE_INPUT_PATH = Path(
    "outputs/active_z2_sigma/background_dimensionless_curvature_scale_inputs.json"
)
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_scale_free_omega_k_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scale_free_omega_k_from_curvature_scale_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scale_free_omega_k_from_curvature_scale_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _validate_base(payload: dict) -> None:
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


def _build_output(sign_payload: dict, scale_payload: dict) -> dict:
    _validate_base(sign_payload)
    _validate_base(scale_payload)
    sign = int(sign_payload["scalars"]["k_Z2Sigma"])
    scale = float(scale_payload["scalars"]["h0_R_curv_over_c_Z2Sigma"])
    omega_k = omega_k_from_dimensionless_curvature_scale(scale, sign)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "omega_k_Z2Sigma": omega_k,
            "h0_R_curv_over_c_Z2Sigma": scale,
            "k_Z2Sigma": sign,
        },
        "scalar_provenance": {
            "omega_k_Z2Sigma": (
                "active_scale_free_curvature:"
                f"k=({sign_payload['scalar_provenance']['k_Z2Sigma']});"
                f"h0Rcurv_over_c=({scale_payload['scalar_provenance']['h0_R_curv_over_c_Z2Sigma']})"
            )
        },
    }


def build_payload(
    *,
    sign_input_path: Path = SIGN_INPUT_PATH,
    scale_input_path: Path = SCALE_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "curvature_sign": sign_input_path.exists(),
        "dimensionless_curvature_scale": scale_input_path.exists(),
    }
    output_written = False
    validation_error = None
    omega_k_value = None
    if all(input_exists.values()):
        try:
            output = _build_output(_load(sign_input_path), _load(scale_input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
            omega_k_value = output["scalars"]["omega_k_Z2Sigma"]
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-scale-free-omega-k-from-curvature-scale-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {
            "curvature_sign": str(sign_input_path),
            "dimensionless_curvature_scale": str(scale_input_path),
        },
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "formula": "omega_k_Z2Sigma = -k_Z2Sigma/(H0_Z2Sigma*R_curv_Z2Sigma/c)^2",
        "omega_k_value": omega_k_value,
        "scale_free_omega_k_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_background_curvature_sign_inputs_json",
            "derive_active_dimensionless_curvature_scale_H0_Rcurv_over_c",
            "supply_outputs_active_z2_sigma_background_dimensionless_curvature_scale_inputs_json",
            "feed_omega_k_Z2Sigma_to_scale_free_background_primitive_manifest",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Scale-Free Omega_k From Curvature Scale Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Formula: `{payload['formula']}`",
        f"Output written: `{payload['scale_free_omega_k_written']}`",
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

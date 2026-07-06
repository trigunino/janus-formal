from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_effective_bao_end_to_end_gate import (
    build_payload as build_end_to_end_payload,
)
from src.janus_lab.z2_sigma_effective_bao import write_effective_scale_free_primitive_inputs
from src.janus_lab.z2_sigma_effective_closure import write_effective_closure_payload
from src.janus_lab.z2_sigma_effective_parameter_inputs import (
    load_effective_bao_parameter_inputs,
)


PARAMETER_INPUT_PATH = Path("outputs/active_z2_sigma/effective_bao_parameter_inputs.json")
CLOSURE_OUTPUT_PATH = Path("outputs/active_z2_sigma/effective_closure_inputs.json")
PRIMITIVE_OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/effective_bao_scale_free_primitive_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_from_parameter_inputs_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_from_parameter_inputs_gate.json"
)


def _write_manifests(
    parameter_payload: dict,
    *,
    closure_output_path: Path,
    primitive_output_path: Path,
) -> None:
    write_effective_closure_payload(
        closure_output_path,
        {
            "active_core": "Z2_tunnel_Sigma",
            "source": "effective_initial_data",
            "compressed_planck_lcdm_used": False,
            "archived_z4_reuse_used": False,
            "observational_fit_used": False,
            "full_no_fit_prediction_ready": False,
            "effective_initial_data": parameter_payload["effective_initial_data"],
            "effective_initial_data_provenance": parameter_payload[
                "effective_initial_data_provenance"
            ],
        },
    )
    z = np.asarray(parameter_payload["z_grid"], dtype=float)
    e_values = np.asarray(parameter_payload["E_Z2Sigma"], dtype=float)
    cs_values = np.asarray(parameter_payload["c_s_over_c_Z2Sigma"], dtype=float)
    gamma_values = np.asarray(parameter_payload["Gamma_drag_over_H0_Z2Sigma"], dtype=float)
    write_effective_scale_free_primitive_inputs(
        primitive_output_path,
        closure_path=closure_output_path,
        z_grid=z,
        e_z2sigma=lambda zz: np.interp(np.asarray(zz, dtype=float), z, e_values),
        cs_over_c_z2sigma=lambda zz: np.interp(np.asarray(zz, dtype=float), z, cs_values),
        gamma_drag_over_h0_z2sigma=lambda zz: np.interp(
            np.asarray(zz, dtype=float), z, gamma_values
        ),
        omega_k_z2sigma=float(parameter_payload["omega_k_Z2Sigma"]),
        primitive_provenance=parameter_payload["primitive_provenance"],
        z_max=float(parameter_payload.get("z_max", z[-1])),
        z_d_bracket=parameter_payload.get("z_d_bracket"),
    )


def build_payload(
    *,
    parameter_input_path: Path = PARAMETER_INPUT_PATH,
    closure_output_path: Path = CLOSURE_OUTPUT_PATH,
    primitive_output_path: Path = PRIMITIVE_OUTPUT_PATH,
) -> dict:
    input_exists = parameter_input_path.exists()
    if not input_exists:
        return {
            "status": "janus-z2-sigma-effective-bao-from-parameter-inputs-gate",
            "active_core": "Z2_tunnel_Sigma",
            "parameter_input_manifest": str(parameter_input_path),
            "parameter_input_exists": False,
            "manifests_written": False,
            "effective_bao_end_to_end_ready": False,
            "full_no_fit_prediction_ready": False,
            "gate_passed": False,
            "primary_blocker": "effective_bao_parameter_inputs_json",
        }
    validation_error = None
    end_to_end = None
    manifests_written = False
    try:
        parameters = load_effective_bao_parameter_inputs(parameter_input_path)
        _write_manifests(
            parameters,
            closure_output_path=closure_output_path,
            primitive_output_path=primitive_output_path,
        )
        manifests_written = True
        end_to_end = build_end_to_end_payload(
            closure_input_path=closure_output_path,
            primitive_input_path=primitive_output_path,
        )
    except Exception as exc:
        validation_error = str(exc)
    ready = bool(end_to_end and end_to_end["gate_passed"])
    return {
        "status": "janus-z2-sigma-effective-bao-from-parameter-inputs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "parameter_input_manifest": str(parameter_input_path),
        "parameter_input_exists": True,
        "closure_output_manifest": str(closure_output_path),
        "primitive_output_manifest": str(primitive_output_path),
        "manifests_written": manifests_written,
        "effective_bao_end_to_end_ready": ready,
        "full_no_fit_prediction_ready": False,
        "chi2_DESI_DR2_BAO_effective": (
            None if end_to_end is None else end_to_end["chi2_DESI_DR2_BAO_effective"]
        ),
        "z_d_Z2Sigma_effective": (
            None if end_to_end is None else end_to_end["z_d_Z2Sigma_effective"]
        ),
        "rhat_d_Z2Sigma_effective": (
            None if end_to_end is None else end_to_end["rhat_d_Z2Sigma_effective"]
        ),
        "gate_passed": ready,
        "primary_blocker": "none" if ready else "effective_parameter_input_validation",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective BAO From Parameter Inputs Gate",
        "",
        f"Parameter input exists: `{payload['parameter_input_exists']}`",
        f"Manifests written: `{payload['manifests_written']}`",
        f"End-to-end ready: `{payload['effective_bao_end_to_end_ready']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
    ]
    if payload.get("chi2_DESI_DR2_BAO_effective") is not None:
        lines.append(f"DESI DR2 BAO effective chi2: `{payload['chi2_DESI_DR2_BAO_effective']}`")
    if payload.get("validation_error"):
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

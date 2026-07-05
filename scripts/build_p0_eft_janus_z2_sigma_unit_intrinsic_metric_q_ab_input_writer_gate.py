from __future__ import annotations

import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


TOPOLOGY_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
GRAVITY_INPUT_PATH = Path("outputs/active_z2_sigma/background_gravity_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_unit_intrinsic_metric_q_ab_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_unit_intrinsic_metric_q_ab_input_writer_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _reject_forbidden(payload: dict) -> None:
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _build_output(rp3: dict, gravity: dict) -> dict:
    if rp3.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("rp3 active_core must be Z2_tunnel_Sigma")
    if rp3.get("source") != "active_derived":
        raise ValueError("rp3 source must be active_derived")
    if gravity.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("gravity active_core must be Z2_tunnel_Sigma")
    if gravity.get("source") != "active_derived":
        raise ValueError("gravity source must be active_derived")
    _reject_forbidden(rp3)
    _reject_forbidden(gravity)

    topology = rp3.get("spatial_topology", {})
    quotient = topology.get("quotient_spatial_slice")
    if quotient not in ["RP3", "S3_paired_leaf_representative"]:
        raise ValueError("quotient_spatial_slice must be RP3 or S3_paired_leaf_representative")

    scalars = gravity.get("scalars", {})
    G = float(scalars["gravitational_constant_si_Z2Sigma"])
    if not math.isfinite(G) or G <= 0.0:
        raise ValueError("gravitational_constant_si_Z2Sigma must be positive")

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "unit_intrinsic_metric_q_ab": [
            [1.0, 0.0, 0.0],
            [0.0, 1.0, 0.0],
            [0.0, 0.0, 1.0],
        ],
        "unit_intrinsic_metric_q_ab_provenance": (
            "active_projective_spatial_unit_orthonormal_throat_chart"
        ),
        "intrinsic_dimension": 3,
        "spatial_topology": topology,
        "kappa_Z2Sigma": 8.0 * math.pi * G,
        "kappa_Z2Sigma_provenance": "8*pi*G from active CODATA gravity convention",
    }


def build_payload(
    *,
    topology_input_path: Path = TOPOLOGY_INPUT_PATH,
    gravity_input_path: Path = GRAVITY_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "projective_spatial_topology_inputs": topology_input_path.exists(),
        "background_gravity_inputs": gravity_input_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build_output(_load(topology_input_path), _load(gravity_input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-unit-intrinsic-metric-q-ab-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "unit_intrinsic_metric_q_ab_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_RP3_slice_and_gravity_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "write_outputs_active_z2_sigma_rp3_spatial_slice_inputs_json",
            "write_outputs_active_z2_sigma_background_gravity_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Unit Intrinsic Metric q_ab Input Writer Gate",
        "",
        f"q_ab written: `{payload['unit_intrinsic_metric_q_ab_written']}`",
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

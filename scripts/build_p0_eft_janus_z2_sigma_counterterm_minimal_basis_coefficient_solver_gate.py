from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_counterterm_minimal_basis_solver import (
    solve_minimal_counterterm_coefficients,
)
from scripts.derive_p0_eft_janus_z2_sigma_cartan_ghy_junction_trace_partition_audit import (
    build_payload as build_partition_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_trace_residual_inputs.json")
Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_minimal_basis_coefficients.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_coefficient_solver_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_coefficient_solver_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _active(payload: dict, name: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{name} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{name} source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"{name} forbidden provenance flag must be false: {key}")


def _sqrt_det_q(q_payload: dict) -> float:
    q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("unit_intrinsic_metric_q_ab must be square")
    det_q = float(np.linalg.det(q))
    if det_q <= 0.0:
        raise ValueError("unit_intrinsic_metric_q_ab must have positive determinant")
    return float(np.sqrt(det_q))


def build_payload(
    *,
    trace_path: Path = INPUT_PATH,
    q_path: Path = Q_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "counterterm_trace_residual_inputs": trace_path.exists(),
        "unit_intrinsic_metric_q_ab": q_path.exists(),
    }
    output_written = False
    validation_error = None
    solution = None
    if all(input_exists.values()):
        try:
            trace = _load(trace_path)
            q_payload = _load(q_path)
            _active(trace, "trace")
            _active(q_payload, "q_payload")
            solution = solve_minimal_counterterm_coefficients(
                R_Sigma_values=trace["R_Sigma_values"],
                R_h_trace_values=trace["R_h_trace_values"],
                R_K_trace_values=trace["R_K_trace_values"],
                kappa_Z2Sigma=q_payload["kappa_Z2Sigma"],
                z2_orientation_sign=trace["z2_orientation_sign"],
                sqrt_det_q=_sqrt_det_q(q_payload),
                noncartan_values=trace.get("E_noncartan_values"),
                enforce_linear_k_partition=bool(
                    trace.get(
                        "linear_K_partition_closed",
                        build_partition_payload()["linear_K_partition_closed"],
                    )
                ),
            )
            manifest = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "fitted_counterterm_coefficient_used": False,
                "a_grid": trace["a_grid"],
                "R_Sigma_values": trace["R_Sigma_values"],
                "linear_K_partition_closed": bool(
                    trace.get(
                        "linear_K_partition_closed",
                        build_partition_payload()["linear_K_partition_closed"],
                    )
                ),
                **solution,
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-minimal-basis-coefficient-solver-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "coefficient_solution_written": output_written,
        "solution": solution,
        "gate_passed": output_written,
        "primary_blocker": "none"
        if output_written
        else next((name for name, exists in input_exists.items() if not exists), "invalid_inputs"),
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_active_R_h_trace_target",
            "derive_active_R_K_trace_target",
            "write_counterterm_trace_residual_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Minimal Basis Coefficient Solver Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["solution"]:
        lines.append(
            f"Coefficient status: `{payload['solution']['coefficient_status']}`"
        )
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

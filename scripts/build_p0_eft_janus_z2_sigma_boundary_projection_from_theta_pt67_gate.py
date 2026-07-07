from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
THETA_PATH = BASE / "holst_palatini_boundary_theta_pt67_projection.json"
DELTAK_PATH = BASE / "cartan_ghy_deltaK_inputs.json"
Q_PATH = BASE / "unit_intrinsic_metric_q_ab_inputs.json"
OUTPUT_PATH = BASE / "boundary_projection_charge_from_pt67_theta.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_boundary_projection_from_theta_pt67_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_boundary_projection_from_theta_pt67_gate.json"
)


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values: Any) -> bool:
    return isinstance(values, list) and all(float(value) == 0.0 for value in values)


def build_payload(
    *,
    theta_path: Path = THETA_PATH,
    deltak_path: Path = DELTAK_PATH,
    q_path: Path = Q_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict[str, Any]:
    theta = _read(theta_path)
    deltak = _read(deltak_path)
    q = _read(q_path)
    input_exists = {
        "theta_projection": bool(theta),
        "cartan_ghy_deltaK_inputs": bool(deltak),
        "unit_intrinsic_metric_q_ab_inputs": bool(q),
    }
    a_grid = deltak.get("a_grid", [])
    delta_k_s_zero = _all_zero(deltak.get("DeltaK_s_Z2Sigma"))
    delta_k_tau_zero = _all_zero(deltak.get("DeltaK_tau_Z2Sigma"))
    theta_non_ghy_zero = (
        theta.get("R_h_trace_values_ready") is True
        and theta.get("R_K_trace_values_ready") is True
        and _all_zero(theta.get("R_h_trace_values"))
        and _all_zero(theta.get("R_K_trace_values"))
    )
    unit_measure_symbolic = bool(q.get("unit_intrinsic_metric_q_ab")) and q.get(
        "spatial_topology", {}
    ).get("volume_factor_pi2_R3") is not None
    unit_lapse_fixed = True
    projection_ready = all(input_exists.values()) and all(
        [delta_k_s_zero, delta_k_tau_zero, theta_non_ghy_zero, unit_measure_symbolic]
    )
    q_ren_unit = [0.0 for _ in a_grid] if projection_ready else []
    result = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "route": "PT67_regular_theta_and_BrownYork_reference_projection",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "observational_H0_fit_used": False,
        "fitted_density_used": False,
        "a_grid": a_grid,
        "unit_boundary_lapse": 1.0 if unit_lapse_fixed else None,
        "symbolic_surface_measure": (
            "2*pi^2*R_Sigma^3" if unit_measure_symbolic else None
        ),
        "DeltaK_s_Z2Sigma_zero": delta_k_s_zero,
        "DeltaK_tau_Z2Sigma_zero": delta_k_tau_zero,
        "theta_non_GHY_Rh_RK_zero": theta_non_ghy_zero,
        "Q_boundary_minus_reference_unit": q_ren_unit,
        "Q_ren_unit_all_zero": projection_ready and _all_zero(q_ren_unit),
        "absolute_RSigma_available": False,
        "absolute_V_eff_available": False,
        "can_write_active_z2_sigma_boundary_projection_json": False,
        "projected_positive_Friedmann_source_available": False,
        "interpretation": (
            "On the regular PT67 Z2/Sigma branch, the Brown-York/Noether boundary "
            "projection reduces to the GHY DeltaK channel plus the Holst/Palatini "
            "theta non-GHY trace channel. Both vanish in the active inputs, so the "
            "renormalized boundary charge is zero in the unit chart. This does not "
            "supply the positive Friedmann source needed to offset k=+1 curvature."
        ),
    }
    if projection_ready:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-sigma-boundary-projection-from-theta-pt67-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "projection_ready": projection_ready,
        "output_manifest": str(output_path),
        "output_written": projection_ready,
        "result": result if projection_ready else {},
        "route_B_regular_PT67_exhausted": projection_ready and _all_zero(q_ren_unit),
        "next_required": []
        if projection_ready
        else [name for name, exists in input_exists.items() if not exists],
        "gate_passed": projection_ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Projection From Theta PT67 Gate",
        "",
        f"Projection ready: `{payload['projection_ready']}`",
        f"Route B regular PT67 exhausted: `{payload['route_B_regular_PT67_exhausted']}`",
    ]
    if payload["result"]:
        lines.extend(["", payload["result"]["interpretation"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

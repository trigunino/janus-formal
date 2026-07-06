from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
RADIUS_PATH = Path("outputs/active_z2_sigma/surface_hk_round_throat_radius_grid_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_normal_flow_geometry_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_normal_flow_from_round_throat.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_normal_flow_from_round_throat.json"
)


FORBIDDEN = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
    "fitted_counterterm_coefficient_used",
]


def _load_active(path: Path, name: str) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{name} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{name} source must be active_derived")
    for key in FORBIDDEN:
        if payload.get(key, False) is not False:
            raise ValueError(f"{name} forbidden provenance flag must be false: {key}")
    return payload


def _build(q_payload: dict, radius_payload: dict) -> dict:
    if radius_payload.get("round_throat_radius_grid_ready") is not True:
        raise ValueError("round_throat_radius_grid_ready must be true")
    q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
    if q.shape != (3, 3) or not np.all(np.isfinite(q)) or not np.allclose(q, q.T):
        raise ValueError("unit_intrinsic_metric_q_ab must be a finite symmetric 3x3 tensor")
    a_grid = np.asarray(radius_payload["a_grid"], dtype=float)
    radius = np.asarray(radius_payload["R_Sigma_values"], dtype=float)
    if a_grid.ndim != 1 or radius.shape != a_grid.shape or a_grid.size < 1:
        raise ValueError("a_grid and R_Sigma_values must be aligned one-dimensional arrays")
    if np.any(radius <= 0.0) or not np.all(np.isfinite(radius)):
        raise ValueError("R_Sigma_values must be positive and finite")
    orientation = float(radius_payload.get("normal_orientation_sign", 1.0))
    if orientation not in (-1.0, 1.0):
        raise ValueError("normal_orientation_sign must be +1.0 or -1.0")

    h_values = []
    k_values = []
    rnabn_values = []
    zero3 = np.zeros((3, 3), dtype=float)
    for r_value in radius:
        h = np.zeros((4, 4), dtype=float)
        h[0, 0] = -1.0
        h[1:, 1:] = (r_value**2) * q
        k = np.zeros((4, 4), dtype=float)
        k[1:, 1:] = orientation * r_value * q
        rnabn = np.zeros((4, 4), dtype=float)
        rnabn[1:, 1:] = zero3
        h_values.append(h.tolist())
        k_values.append(k.tolist())
        rnabn_values.append(rnabn.tolist())

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "a_grid": a_grid.tolist(),
        "R_Sigma_values": radius.tolist(),
        "induced_metric_h_ab": h_values,
        "extrinsic_curvature_K_ab": k_values,
        "normal_riemann_R_nabn": rnabn_values,
        "normal_orientation": f"{orientation:+.0f}",
        "normal_orientation_sign": orientation,
        "sign_conventions": {
            "metric_signature": "mostly_plus_on_Sigma",
            "round_throat_h_ab": "diag(-1, R_Sigma^2 q_ij)",
            "round_throat_K_ij": "normal_orientation_sign * R_Sigma q_ij",
            "round_throat_K_tau_tau": "0",
            "normal_riemann_R_nabn": "0 for the local round product collar",
            "normal_flow": "partial_R h_ab = 2 K_ab; partial_R K_ab = R_nabn + K_a^c K_cb",
        },
        "geometry_provenance": radius_payload.get(
            "geometry_provenance",
            "round Z2/Sigma throat local normal-flow geometry from explicit radius grid",
        ),
    }


def build_payload(
    *,
    q_path: Path = Q_PATH,
    radius_path: Path = RADIUS_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "unit_intrinsic_metric_q_ab": q_path.exists(),
        "surface_hk_round_throat_radius_grid_inputs": radius_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build(
                _load_active(q_path, "q_payload"),
                _load_active(radius_path, "radius_payload"),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-surface-hk-normal-flow-from-round-throat",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "normal_flow_geometry_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none"
        if output_written
        else next((name for name, exists in input_exists.items() if not exists), "invalid_inputs"),
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_or_supply_surface_hk_round_throat_radius_grid_inputs",
            "do_not_guess_R_Sigma_values",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Normal Flow From Round Throat",
        "",
        f"Output written: `{payload['normal_flow_geometry_written']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

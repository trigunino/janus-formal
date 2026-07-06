from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_global_regularity_primitives import (
    validate_and_materialize_freg_components,
)


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_round_product_probe.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_round_product_probe.json")


def _load_q(path: Path) -> np.ndarray:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("q active_core must be Z2_tunnel_Sigma")
    q = np.asarray(payload["unit_intrinsic_metric_q_ab"], dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1] or np.linalg.det(q) <= 0.0:
        raise ValueError("unit_intrinsic_metric_q_ab must be positive square")
    return q


def build_payload(
    *,
    q_path: Path = Q_PATH,
    lambda_grid: tuple[float, ...] = (0.5, 1.0, 2.0),
    u_grid: tuple[float, ...] = (0.0, 1.0),
) -> dict:
    q = _load_q(q_path)
    lambdas = np.asarray(lambda_grid, dtype=float)
    u = np.asarray(u_grid, dtype=float)
    dim = q.shape[0]
    endpoint_metrics = np.asarray([lam * lam * q for lam in lambdas], dtype=float)
    primitive = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_global_regularity_primitives",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": lambdas.tolist(),
        "collar_coordinate_u_grid": u.tolist(),
        "normal_connection_omega_perp_lambda_u": np.zeros(
            (lambdas.size, u.size, dim, dim), dtype=float
        ).tolist(),
        "deck_frame_map_lambda": np.repeat(np.eye(dim)[None, :, :], lambdas.size, axis=0).tolist(),
        "h_plus_endpoint_lambda": endpoint_metrics.tolist(),
        "h_minus_endpoint_lambda": endpoint_metrics.tolist(),
        "tau_Z2_pullback_matrix_on_endpoint_tangents": np.repeat(
            np.eye(dim)[None, :, :], lambdas.size, axis=0
        ).tolist(),
        "endpoint_metric_norm": [
            float(np.sum(metric * metric)) for metric in endpoint_metrics
        ],
        "S_Sigma_divergence_lambda": np.zeros((lambdas.size, dim), dtype=float).tolist(),
        "bulk_normal_flux_jump_lambda": np.zeros((lambdas.size, dim), dtype=float).tolist(),
        "surface_vector_norm": [1.0 for _ in lambdas],
        "root_tolerance": 1.0e-12,
        "primitive_provenance": {
            "normal_connection_omega_perp_lambda_u": "active_round_product_collar_zero_normal_connection",
            "endpoint_collar_metrics_and_z2_pullback": "active_round_product_collar_identity_deck_pullback",
            "sigma_stress_and_bulk_normal_flux": "active_round_product_collar_transparent_bianchi_probe",
        },
    }
    freg = validate_and_materialize_freg_components(primitive)
    return {
        "status": "janus-z2-sigma-global-regular-round-product-probe",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_probe",
        "extension_allowed": False,
        "round_product_collar_assumptions": {
            "normal_connection": "0",
            "deck_frame_map": "identity",
            "h_plus_endpoint": "lambda^2 q_ab",
            "h_minus_endpoint": "lambda^2 q_ab",
            "tau_Z2_pullback": "identity_on_endpoint_tangents",
            "junction_bianchi_residual": "0",
        },
        "F_reg": freg["F_reg"],
        "regularity_roots": freg["regularity_roots"],
        "R_Sigma_over_ell_collar_selected": freg["R_Sigma_over_ell_collar_selected"],
        "radius_selection_ready": False,
        "interpretation": (
            "The local round product collar has zero holonomy, endpoint and Bianchi "
            "defects for every sampled lambda. Its regularity functional is flat, "
            "so it cannot select a unique throat radius."
        ),
        "next_required": [
            "derive_nontrivial_active_collar_connection_or_endpoint_deck_mismatch",
            "or_accept_R_Sigma_as_modulus_until_new_surface_dynamics_is_derived",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Global Regular Round Product Probe",
        "",
        f"Selected unique ratio: `{payload['R_Sigma_over_ell_collar_selected']}`",
        f"F_reg: `{payload['F_reg']}`",
        "",
        payload["interpretation"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

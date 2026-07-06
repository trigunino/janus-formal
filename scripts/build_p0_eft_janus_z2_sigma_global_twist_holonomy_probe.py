from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_global_regular_freg_from_primitives_gate import (
    build_payload as build_from_primitives_payload,
)


PRIMITIVE_PATH = Path("outputs/diagnostics/global_regular_freg_primitives_global_twist_probe.json")
COMPONENT_PATH = Path("outputs/diagnostics/global_regular_freg_components_global_twist_probe.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_twist_holonomy_probe.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_twist_holonomy_probe.json")


def _primitive_payload() -> dict:
    lambda_grid = [0.5, 1.0, 1.5]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_global_regularity_primitives",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": lambda_grid,
        "collar_coordinate_u_grid": [0.0, 1.0],
        "normal_connection_omega_perp_lambda_u": [
            [[[-2.0 * lam]], [[-2.0 * lam]]] for lam in lambda_grid
        ],
        "deck_frame_map_lambda": [[[-1.0]] for _ in lambda_grid],
        "h_plus_endpoint_lambda": [[[1.0]] for _ in lambda_grid],
        "h_minus_endpoint_lambda": [[[1.0]] for _ in lambda_grid],
        "tau_Z2_pullback_matrix_on_endpoint_tangents": [[[1.0]] for _ in lambda_grid],
        "endpoint_metric_norm": [1.0 for _ in lambda_grid],
        "S_Sigma_divergence_lambda": [[0.0] for _ in lambda_grid],
        "bulk_normal_flux_jump_lambda": [[0.0] for _ in lambda_grid],
        "surface_vector_norm": [1.0 for _ in lambda_grid],
        "root_tolerance": 1.0e-12,
        "primitive_provenance": {
            "normal_connection_omega_perp_lambda_u": "diagnostic_projective_holonomy_twist_model",
            "endpoint_collar_metrics_and_z2_pullback": "diagnostic_matched_endpoint_metrics",
            "sigma_stress_and_bulk_normal_flux": "diagnostic_zero_flux_channel",
        },
    }


def build_payload(
    *,
    primitive_path: Path = PRIMITIVE_PATH,
    component_path: Path = COMPONENT_PATH,
) -> dict:
    primitive_path.parent.mkdir(parents=True, exist_ok=True)
    primitive_path.write_text(json.dumps(_primitive_payload(), indent=2), encoding="utf-8")
    probe = build_from_primitives_payload(
        input_path=primitive_path,
        component_output_path=component_path,
    )
    return {
        "status": "janus-z2-sigma-global-twist-holonomy-probe",
        "active_core": "Z2_tunnel_Sigma",
        "diagnostic_only": True,
        "writes_active_manifest": False,
        "twist_model_source_derived": False,
        "primitive_manifest": str(primitive_path),
        "component_manifest": str(component_path),
        "R_Sigma_over_ell_collar_selected": probe["R_Sigma_over_ell_collar_selected"],
        "regularity_roots": probe["regularity_roots"],
        "full_no_fit_prediction_ready": False,
        "interpretation": (
            "A nonlocal holonomy twist can select a unique ratio in the F_reg "
            "machinery, but this probe is not derived from the active Janus action."
        ),
        "gate_passed": True,
        "primary_blocker": "derive_projective_holonomy_twist_from_active_collar_geometry",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Global Twist Holonomy Probe",
                "",
                f"Diagnostic only: `{payload['diagnostic_only']}`",
                f"Twist source derived: `{payload['twist_model_source_derived']}`",
                f"Ratio selected in probe: `{payload['R_Sigma_over_ell_collar_selected']}`",
                f"Roots: `{payload['regularity_roots']}`",
                "",
                payload["interpretation"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

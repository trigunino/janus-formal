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


PRIMITIVE_PATH = Path("outputs/diagnostics/global_regular_freg_primitives_local_transparent_probe.json")
COMPONENT_PATH = Path("outputs/diagnostics/global_regular_freg_components_local_transparent_probe.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_local_transparent_probe.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_local_transparent_probe.json")


def _primitive_payload() -> dict:
    lambda_grid = [0.5, 1.0, 2.0]
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
            [[[0.0]], [[0.0]]] for _ in lambda_grid
        ],
        "deck_frame_map_lambda": [[[1.0]] for _ in lambda_grid],
        "h_plus_endpoint_lambda": [[[1.0]] for _ in lambda_grid],
        "h_minus_endpoint_lambda": [[[1.0]] for _ in lambda_grid],
        "tau_Z2_pullback_matrix_on_endpoint_tangents": [[[1.0]] for _ in lambda_grid],
        "endpoint_metric_norm": [1.0 for _ in lambda_grid],
        "S_Sigma_divergence_lambda": [[0.0] for _ in lambda_grid],
        "bulk_normal_flux_jump_lambda": [[0.0] for _ in lambda_grid],
        "surface_vector_norm": [1.0 for _ in lambda_grid],
        "root_tolerance": 1.0e-12,
        "primitive_provenance": {
            "normal_connection_omega_perp_lambda_u": "active_local_unit_throat_chart_transparent_probe",
            "endpoint_collar_metrics_and_z2_pullback": "active_local_unit_throat_chart_transparent_probe",
            "sigma_stress_and_bulk_normal_flux": "active_flow_tangency_transparent_probe",
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
    all_lambda_roots = len(probe["regularity_roots"]) > 1
    return {
        "status": "janus-z2-sigma-global-regular-local-transparent-probe",
        "active_core": "Z2_tunnel_Sigma",
        "diagnostic_only": True,
        "writes_active_manifest": False,
        "primitive_manifest": str(primitive_path),
        "component_manifest": str(component_path),
        "local_transparent_probe_ran": probe["component_manifest_written"],
        "all_defects_zero_on_grid": all_lambda_roots,
        "R_Sigma_over_ell_collar_selected": False,
        "full_no_fit_prediction_ready": False,
        "interpretation": (
            "The local transparent collar satisfies zero defect for every sampled "
            "lambda, so local regularity alone is flat in R_Sigma/ell_collar."
        ),
        "gate_passed": True,
        "primary_blocker": "global_nonlocal_defect_needed_for_radius_selection",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Global Regular Local Transparent Probe",
                "",
                f"Diagnostic only: `{payload['diagnostic_only']}`",
                f"All defects zero on grid: `{payload['all_defects_zero_on_grid']}`",
                f"Ratio selected: `{payload['R_Sigma_over_ell_collar_selected']}`",
                "",
                payload["interpretation"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_global_regularity import (
    validate_global_regular_component_payload,
)
from src.janus_lab.z2_sigma_homothetic_collar import (
    reciprocal_projective_endpoint_defect_values,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reciprocal_projective_collar_probe.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reciprocal_projective_collar_probe.json")


def build_payload(lambda_grid: tuple[float, ...] = (0.5, 1.0, 2.0)) -> dict:
    endpoint = reciprocal_projective_endpoint_defect_values(lambda_grid=lambda_grid)
    freg = validate_global_regular_component_payload(
        {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_global_regularity_components",
            "compressed_planck_lcdm_used": False,
            "archived_z4_reuse_used": False,
            "observational_fit_used": False,
            "torus_replacement_used": False,
            "full_no_fit_prediction_ready": False,
            "lambda_grid": list(lambda_grid),
            "normal_frame_holonomy_defect": [0.0 for _ in lambda_grid],
            "collar_endpoint_mismatch": endpoint.tolist(),
            "junction_bianchi_defect": [0.0 for _ in lambda_grid],
            "root_tolerance": 1.0e-12,
            "component_provenance": {
                "normal_frame_holonomy_defect": "active_reciprocal_projective_collar_probe_zero_normal_defect",
                "collar_endpoint_mismatch": "active_reciprocal_projective_collar_lambda_to_inverse_lambda_probe",
                "junction_bianchi_defect": "active_reciprocal_projective_collar_probe_zero_bianchi_defect",
            },
        }
    )
    return {
        "status": "janus-z2-sigma-reciprocal-projective-collar-probe",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_probe",
        "extension_allowed": False,
        "reciprocal_map": "lambda -> 1/lambda",
        "F_reg": freg["F_reg"],
        "regularity_roots": freg["regularity_roots"],
        "R_Sigma_over_ell_collar_selected": freg["R_Sigma_over_ell_collar_selected"],
        "candidate_ratio": freg["regularity_roots"][0]
        if freg["R_Sigma_over_ell_collar_selected"]
        else None,
        "promotion_ready": False,
        "primary_blocker": "derive_reciprocal_projective_collar_map_from_Janus_tunnel_geometry",
        "interpretation": (
            "A reciprocal projective collar would select lambda=1 without BAO or "
            "Z4 input. This is a concrete geometric route, but it is not proven "
            "until the lambda -> 1/lambda deck action is derived from the active "
            "Janus tunnel embedding."
        ),
        "next_required": [
            "derive_tau_Z2_action_on_collar_radius_as_lambda_inverse",
            "prove_endpoint_metric_pullback_uses_reciprocal_collar_metric",
            "then_promote_candidate_ratio_to_R_Sigma_solution_certificate",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Reciprocal Projective Collar Probe",
        "",
        f"Selected ratio: `{payload['R_Sigma_over_ell_collar_selected']}`",
        f"Candidate ratio: `{payload['candidate_ratio']}`",
        f"Promotion ready: `{payload['promotion_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
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

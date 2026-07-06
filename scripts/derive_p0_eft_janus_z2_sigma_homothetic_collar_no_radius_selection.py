from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_global_regular_round_product_probe import (
    _load_q,
)
from src.janus_lab.z2_sigma_homothetic_collar import (
    homothetic_collar_radius_selection_status,
    homothetic_constant_regular_payload,
    homothetic_endpoint_defect_values,
)


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_homothetic_collar_no_radius_selection.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_homothetic_collar_no_radius_selection.json")


def build_payload(
    *,
    q_path: Path = Q_PATH,
    lambda_grid: tuple[float, ...] = (0.5, 1.0, 2.0),
) -> dict:
    q = _load_q(q_path)
    lambdas = np.asarray(lambda_grid, dtype=float)
    dim = q.shape[0]
    identity_endpoint = homothetic_endpoint_defect_values(
        lambda_grid=lambdas,
        q_plus=q,
        q_minus=q,
        tau_pullback=np.eye(dim),
    )
    twist_endpoint = homothetic_endpoint_defect_values(
        lambda_grid=lambdas,
        q_plus=q,
        q_minus=q,
        tau_pullback=-np.eye(dim),
    )
    anisotropic_q_minus = q.copy()
    anisotropic_q_minus[0, 0] *= 1.2
    mismatch_endpoint = homothetic_endpoint_defect_values(
        lambda_grid=lambdas,
        q_plus=q,
        q_minus=anisotropic_q_minus,
        tau_pullback=np.eye(dim),
    )
    cases = {
        "identity_round_product": homothetic_constant_regular_payload(
            lambda_grid=lambdas,
            endpoint_defect=identity_endpoint,
        ),
        "projective_sign_twist": homothetic_constant_regular_payload(
            lambda_grid=lambdas,
            endpoint_defect=twist_endpoint,
            normal_holonomy_defect=4.0,
        ),
        "homothetic_endpoint_mismatch": homothetic_constant_regular_payload(
            lambda_grid=lambdas,
            endpoint_defect=mismatch_endpoint,
        ),
    }
    statuses = {
        name: homothetic_collar_radius_selection_status(case["F_reg"])
        for name, case in cases.items()
    }
    return {
        "status": "janus-z2-sigma-homothetic-collar-no-radius-selection",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_derivation",
        "extension_allowed": False,
        "homothetic_class": "h_plus(lambda)=lambda^2 q_plus, h_minus(lambda)=lambda^2 q_minus",
        "assumptions": {
            "tau_Z2_pullback_lambda_dependence": "none",
            "deck_frame_map_lambda_dependence": "none",
            "normal_connection_defect_lambda_dependence": "none",
            "junction_bianchi_defect_lambda_dependence": "none",
        },
        "case_F_reg": {name: case["F_reg"] for name, case in cases.items()},
        "case_status": statuses,
        "radius_selection_ready": False,
        "R_Sigma_solution_certificate_ready": False,
        "conclusion": (
            "Every homothetic collar with lambda-independent deck/pullback/defect "
            "data gives lambda-independent F_reg. This class cannot select a "
            "unique R_Sigma/ell_collar."
        ),
        "next_required": [
            "derive_nonhomothetic_active_collar_metric",
            "or_derive_lambda_dependent_normal_connection_from_full_tunnel_embedding",
            "or_derive_surface_dynamics_coefficients_a0_a1_a2_a3",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Homothetic Collar No Radius Selection",
        "",
        f"Radius selection ready: `{payload['radius_selection_ready']}`",
        "",
        payload["conclusion"],
        "",
        "## Cases",
    ]
    for name, values in payload["case_F_reg"].items():
        status = payload["case_status"][name]
        lines.append(
            f"- `{name}`: F_reg=`{values}`, constant=`{status['F_reg_lambda_independent']}`"
        )
    lines.extend(["", "## Next Required"])
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

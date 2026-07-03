from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_flrw_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_flrw_projection_gate.json")


def build_payload() -> dict:
    algebraic = {
        "brown_york_cartan_GHY_convention_declared": True,
        "FLRW_induced_metric_declared": True,
        "Z2_normal_orientation_declared": True,
        "extrinsic_curvature_scalars_declared": True,
        "tunnel_embedding_extrinsic_curvature_structural_closure_ready": True,
        "Delta_Ks_projection_formula_ready": True,
        "Delta_Ktau_projection_formula_ready": True,
        "rho_CartanGHY_formula_ready": True,
        "p_CartanGHY_formula_ready": True,
    }
    scale_factor = {
        "Delta_Ks_of_a_ready": False,
        "Delta_Ktau_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-cartan-ghy-flrw-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_result": (
            "Brown-York/Israel machinery supplies the algebraic FLRW projection; "
            "Janus-specific tunnel embedding functions are still local derivations."
        ),
        "algebraic": algebraic,
        "scale_factor": scale_factor,
        "formulas": {
            "rho_CartanGHY": "rho_CGHY(a) = 3 * eps_Z2 * DeltaK_s(a) / kappa",
            "p_CartanGHY": "p_CGHY(a) = eps_Z2 * (DeltaK_tau(a) - 2 * DeltaK_s(a)) / kappa",
            "DeltaK_s": "spatial FLRW extrinsic-curvature jump across Sigma",
            "DeltaK_tau": "timelike FLRW extrinsic-curvature jump across Sigma",
        },
        "cartan_GHY_FLRW_algebraic_projection_ready": all(algebraic.values()),
        "cartan_GHY_FLRW_scale_factor_closure_ready": all(algebraic.values())
        and all(scale_factor.values()),
        "next_required": [
            "derive_DeltaK_s_of_a_from_Z2_tunnel_embedding",
            "derive_DeltaK_tau_of_a_from_Z2_tunnel_embedding",
            "propagate_Z2_normal_orientation_sign_into_total_T_eff_ab",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY FLRW Projection Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Algebraic projection ready: `{payload['cartan_GHY_FLRW_algebraic_projection_ready']}`",
        f"Scale-factor closure ready: `{payload['cartan_GHY_FLRW_scale_factor_closure_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

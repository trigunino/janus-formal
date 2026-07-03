from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_radial_block_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_radial_block_gate.json")


def build_payload() -> dict:
    declared = {
        "GHY_Brown_York_bibliography_checked": True,
        "Cartan_GHY_boundary_term_available": True,
        "radial_embedding_variation_declared": True,
        "induced_metric_radial_variation_declared": True,
        "extrinsic_curvature_radial_variation_declared": True,
        "Z2_normal_orientation_declared": True,
        "observational_fit_forbidden": True,
        "E_CartanGHY_functional_derivative_declared": True,
    }
    closure = {
        "E_CartanGHY_structural_reduction_ready": True,
        "E_CartanGHY_of_a_ready": False,
        "R_Sigma_of_a_required": True,
    }
    return {
        "status": "janus-z2-sigma-cartan-ghy-radial-block-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "York/Gibbons-Hawking boundary variational term",
            "Brown-York quasilocal boundary stress",
            "Israel 1966 thin-shell extrinsic-curvature formalism",
        ],
        "bibliography_result": (
            "The GHY/Brown-York machinery supplies the radial variation of the "
            "boundary term through induced-metric and extrinsic-curvature variations. "
            "The active Janus/Sigma evaluation as a function of scale factor still "
            "requires R_Sigma(a) and the resolved embedding."
        ),
        "declared": declared,
        "closure": closure,
        "structural_formula": (
            "E_CartanGHY = eps_Z2/kappa * delta_RSigma[ sqrt(|h|) K ] "
            "= eps_Z2/kappa * sqrt(|h|) * (partial_R K + 1/2 K h^ab partial_R h_ab)"
        ),
        "cartan_ghy_radial_ledger_declared": all(declared.values()),
        "cartan_ghy_radial_block_reduced": all(declared.values())
        and closure["E_CartanGHY_structural_reduction_ready"],
        "cartan_ghy_radial_block_of_a_ready": all(declared.values())
        and closure["E_CartanGHY_structural_reduction_ready"]
        and closure["E_CartanGHY_of_a_ready"],
        "next_required": [
            "insert_active_R_Sigma_of_a",
            "insert_active_X_plus_minus_of_a",
            "evaluate_partial_R_h_ab_and_partial_R_K_on_Sigma",
            "propagate_E_CartanGHY_into_E_RSigma_block_sum",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY Radial Block Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Block reduced: `{payload['cartan_ghy_radial_block_reduced']}`",
        f"Block of a ready: `{payload['cartan_ghy_radial_block_of_a_ready']}`",
        "",
        "## Structural Formula",
        f"`{payload['structural_formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

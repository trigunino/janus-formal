from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_no_extension_charge_normalization_no_go_gate import (
    build_payload as build_charge_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_aps_pin_projected_charge_selection_audit_gate import (
    build_payload as build_aps_charge_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_collar_reduction_surface_intrinsic_curvature_no_extension_gate import (
    build_payload as build_collar_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_regular_throat_radius_condition_audit_gate import (
    build_payload as build_regular_throat_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_rsigma_observable_modulus_audit_gate import (
    build_payload as build_rsigma_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_no_extension_frontier_summary_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_no_extension_frontier_summary_gate.json"
)


def build_payload() -> dict:
    rsigma = build_rsigma_payload()
    charge = build_charge_payload()
    collar = build_collar_payload()
    regularity = build_regular_throat_payload()
    aps_charge = build_aps_charge_payload()
    blockers = {
        "R_Sigma_modulus": {
            "open": bool(rsigma["R_Sigma_modulus_open"]),
            "blocks_dimensional_pipeline": bool(
                rsigma["official_dimensional_branch_requires_radius_or_scale_input"]
            ),
            "scale_free_escape_available": bool(
                rsigma["scale_free_branch_can_be_pursued_without_extension"]
            ),
        },
        "projected_baryon_charge": {
            "open": bool(
                not charge["derivable_without_extra_input"]["absolute_N_Z2Sigma"]
            ),
            "blocks_scale_free_BAO_primitive": bool(
                not charge["consequence"]["scale_free_BAO_primitive_ready"]
            ),
            "blocks_early_plasma_baryon_density": bool(
                not charge["consequence"][
                    "early_plasma_baryon_density_no_extension_ready"
                ]
            ),
        },
    }
    no_extension_routes = {
        "collar_reduction_to_surface_Rh": {
            "operator_found": collar["checks"][
                "surface_intrinsic_Rh_generated_by_formal_reduction"
            ],
            "coefficient_fixed": collar["checks"][
                "coefficient_fixed_by_existing_action_alone"
            ],
            "primary_blocker": collar["primary_blocker"],
        },
        "regular_throat_condition": {
            "parity_constraints_found": regularity["derivable"][
                "parity_of_h_ab_under_normal_reflection"
            ],
            "R_Sigma_fixed": regularity["derivable"]["absolute_R_Sigma_value"],
            "primary_blocker": regularity["primary_blocker"],
        },
        "APS_Pin_projected_charge_selection": {
            "charge_class_constraints_found": aps_charge["aps_pin_can_fix"][
                "allowed_charge_parity_or_integrality_class"
            ],
            "absolute_charge_fixed": not aps_charge[
                "aps_pin_cannot_fix_without_state_input"
            ]["absolute_projected_baryon_Noether_charge"],
            "primary_blocker": aps_charge["primary_blocker"],
        },
    }
    no_extension_exhausted = (
        blockers["R_Sigma_modulus"]["open"]
        and blockers["projected_baryon_charge"]["open"]
    )
    return {
        "status": "janus-z2-sigma-no-extension-frontier-summary-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_no_extension_audit",
        "policy": {
            "extension_allowed": False,
            "observational_fit_allowed": False,
            "compressed_planck_lcdm_allowed": False,
            "archived_z4_reuse_allowed": False,
        },
        "blockers": blockers,
        "no_extension_routes_tested": no_extension_routes,
        "positive_closure_retained": {
            "projective_Z2_topology": True,
            "tunnel_Sigma_cycle": True,
            "sqrt_Rh_cancels_local_Cartan_GHY_radial_block": True,
            "Dirac_current_projection_and_conservation": True,
        },
        "no_extension_route_exhausted_for_observational_BAO": no_extension_exhausted,
        "full_no_fit_prediction_ready": False,
        "gate_passed": True,
        "primary_blockers": [
            "R_Sigma_not_fixed_by_existing_action",
            "absolute_projected_Noether_charge_not_fixed",
            collar["primary_blocker"],
            regularity["primary_blocker"],
            aps_charge["primary_blocker"],
        ],
        "allowed_next_without_extension": [
            "document the open moduli",
            "restrict claims to topology/local identities independent of R_Sigma and baryon normalization",
            "search for a genuine theorem fixing projected Noether charge or R_Sigma inside the existing action",
        ],
        "forbidden_next_without_new_theorem": [
            "choose R_Sigma by BAO fit",
            "choose baryon density by Planck/LambdaCDM compression",
            "add C R[h] or other Sigma density as an extension",
            "reuse archived Z4 phenomenology as active proof",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma No-Extension Frontier Summary Gate",
        "",
        f"No-extension route exhausted for observational BAO: `{payload['no_extension_route_exhausted_for_observational_BAO']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        "",
        "## Primary Blockers",
    ]
    lines.extend(f"- `{item}`" for item in payload["primary_blockers"])
    lines.extend(["", "## Allowed Next Without Extension"])
    lines.extend(f"- `{item}`" for item in payload["allowed_next_without_extension"])
    lines.extend(["", "## Forbidden Without New Theorem"])
    lines.extend(f"- `{item}`" for item in payload["forbidden_next_without_new_theorem"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

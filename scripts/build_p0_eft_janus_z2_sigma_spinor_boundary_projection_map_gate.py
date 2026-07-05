from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flux_projection_domain_gate import (
    build_payload as build_flux_projection_domain_payload,
)
from scripts.build_p0_eft_janus_sigma_aps_pin_lift_obligation_gate import (
    build_payload as build_sigma_aps_pin_lift_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_boundary_spinor_restriction_gate import (
    build_payload as build_boundary_spinor_restriction_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_tangent_normal_orientation_gate import (
    build_payload as build_tangent_normal_orientation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import (
    build_payload as build_projective_gluing_normal_orientation_sign_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_local_mit_reflecting_projector_gate import (
    build_payload as build_local_mit_projector_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate.json")


def build_payload() -> dict:
    flux_domain = build_flux_projection_domain_payload()
    aps_pin = build_sigma_aps_pin_lift_payload()
    boundary_spinor = build_boundary_spinor_restriction_payload()
    tangent_normal = build_tangent_normal_orientation_payload()
    normal_orientation_sign = build_projective_gluing_normal_orientation_sign_payload()
    local_mit = build_local_mit_projector_payload()
    coorientation_ready = flux_domain["closure"]["coorientation_ready"]
    sigma_aps_ready = aps_pin["sigma_aps_boundary_pin_lift_closed"]
    boundary_spinor_ready = boundary_spinor["boundary_spinor_restriction_ready"]
    tangent_normal_ready = tangent_normal["tangent_normal_orientation_ready"]
    z2_normal_orientation_ready = normal_orientation_sign[
        "projective_gluing_normal_orientation_sign_ready"
    ]
    declared = {
        "APS_projection_bibliography_checked": True,
        "local_boundary_projection_bibliography_checked": True,
        "boundary_spinor_restriction_gate_declared": True,
        "APS_Pin_lift_input_imported": True,
        "Z2_normal_orientation_input_imported": True,
        "projection_map_declared": True,
        "no_free_boundary_phase": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "boundary_spinor_restriction_ready": boundary_spinor_ready,
        "Sigma_boundary_spinor_data_ready": boundary_spinor["closure"]["Sigma_boundary_spinor_data_ready"],
        "Sigma_APS_boundary_Pin_lift_closed": sigma_aps_ready,
        "Z2_coorientation_sign_ready": coorientation_ready,
        "tangent_normal_orientation_ready": tangent_normal_ready,
        "Z2_normal_orientation_ready": z2_normal_orientation_ready,
        "unit_normal_Clifford_action_ready": local_mit["closure"][
            "unit_normal_Clifford_action_ready"
        ],
        "projection_idempotent_ready": local_mit["closure"]["projection_idempotent_ready"],
        "projection_self_adjoint_ready": local_mit["closure"]["projection_self_adjoint_ready"],
        "Z2Sigma_spinor_projection_ready": boundary_spinor_ready
        and local_mit["local_mit_reflecting_projector_ready"],
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = (
        "none"
        if ready
        else tangent_normal.get("primary_blocker")
        or flux_domain.get("primary_blocker")
        or "boundary_spinor_data_and_unit_normal_clifford_action"
    )
    return {
        "status": "janus-z2-sigma-spinor-boundary-projection-map-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "APS spectral boundary projectors for Dirac operators",
            "local MIT/chiral bag boundary projectors using normal Clifford action",
            "active Sigma APS/Pin and Z2 normal-orientation gates",
        ],
        "bibliography_result": (
            "Generic Dirac boundary theory supplies spectral and local projector "
            "machinery. It does not supply the active Janus Z2/Sigma projector or "
            "its fixed phase/sign conventions."
        ),
        "source_links": [
            "https://webhomes.maths.ed.ac.uk/~v1ranick/papers/aps001.pdf",
            "https://arxiv.org/html/2412.17396v1",
            "https://hal.science/hal-00021463/document",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "flux_projection_domain": {
                "gate": flux_domain["status"],
                "ready": flux_domain["flux_projection_domain_ready"],
                "closure": flux_domain["closure"],
                "primary_blocker": flux_domain.get("primary_blocker"),
            },
            "sigma_aps_pin_lift": {
                "gate": aps_pin["status"],
                "ready": aps_pin["sigma_aps_boundary_pin_lift_closed"],
            },
            "boundary_spinor_restriction": {
                "gate": boundary_spinor["status"],
                "ready": boundary_spinor["boundary_spinor_restriction_ready"],
                "closure": boundary_spinor["closure"],
            },
            "tangent_normal_orientation": {
                "gate": tangent_normal["status"],
                "ready": tangent_normal["tangent_normal_orientation_ready"],
                "closure": tangent_normal["closure"],
                "primary_blocker": tangent_normal.get("primary_blocker"),
            },
            "projective_gluing_normal_orientation_sign": {
                "gate": normal_orientation_sign["status"],
                "ready": normal_orientation_sign[
                    "projective_gluing_normal_orientation_sign_ready"
                ],
                "formulae": normal_orientation_sign["formulae"],
            },
            "local_mit_reflecting_projector": {
                "gate": local_mit["status"],
                "ready": local_mit["local_mit_reflecting_projector_ready"],
                "closure": local_mit["closure"],
                "scope": local_mit["scope"],
            },
        },
        "partial_subchannels": {
            "Z2_coorientation_sign": {
                "ready": coorientation_ready,
                "status": "partial_only_not_unit_normal_clifford_ready",
            },
            "Sigma_APS_Pin_lift": {
                "ready": sigma_aps_ready,
                "status": "closed_upstream_not_the_projection_map",
            },
            "Z2_normal_orientation_sign": {
                "ready": z2_normal_orientation_ready,
                "status": "orientation_sign_ready",
            },
            "local_MIT_projector": {
                "ready": local_mit["local_mit_reflecting_projector_ready"],
                "status": "local_projector_algebra_only_not_boundary_spinor_data",
            },
        },
        "nearest_spinor_projection_frontier": {
            "block": "boundary_spinor_data_and_unit_normal_clifford_action",
            "gates": [
                "P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate",
                "P0EFTJanusZ2SigmaTangentNormalOrientationGate",
            ],
            "diagnostic_only": True,
        },
        "formulas": {
            "projection_map": "psi_Sigma^Z2 = P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, n_Z2, APS/Pin data)",
            "normal_clifford_action": "gamma(n_Z2) acts on restricted spinors only after active unit normal data exist",
            "idempotence_guard": "P_Z2Sigma^2 = P_Z2Sigma",
            "adjoint_guard": "P_Z2Sigma^dagger = P_Z2Sigma",
            "phase_policy": "no fitted boundary phase or free chiral bag angle",
        },
        "spinor_boundary_projection_map_ledger_declared": all(declared.values()),
        "spinor_boundary_projection_map_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "pass_boundary_spinor_restriction_gate",
            "close_sigma_APS_Pin_lift",
            "derive_Z2_normal_orientation",
            "derive_boundary_spinor_data_from_plus_minus_spinor_bundles",
            "feed_projection_map_to_spinor_bundle_projection_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spinor Boundary Projection Map Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['spinor_boundary_projection_map_ledger_declared']}`",
        f"Projection map ready: `{payload['spinor_boundary_projection_map_ready']}`",
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

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_spinor_bundle_data_gate import (
    build_payload as build_spinor_bundle_data_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_local_pin_reflection_intertwiner_gate import (
    build_payload as build_local_intertwiner_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_soldering_equivariance_from_boundary_variation_gate import (
    build_payload as build_soldering_equivariance_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_quotient_descent_equivariance_gate import (
    build_payload as build_quotient_descent_equivariance_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_current_parity_from_spinor_intertwiner_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_current_parity_from_spinor_intertwiner_gate.json")


def build_payload() -> dict:
    spinor_bundle = build_spinor_bundle_data_payload()
    local_intertwiner = build_local_intertwiner_payload()
    soldering_equivariance = build_soldering_equivariance_payload()
    quotient_descent_equivariance = build_quotient_descent_equivariance_payload()
    physical_equivariance_ready = (
        soldering_equivariance["physical_spinor_equivariance_from_boundary_variation_ready"]
        or quotient_descent_equivariance[
            "physical_spinor_equivariance_from_quotient_descent_ready"
        ]
    )
    declared = {
        "Pin_Clifford_covariance_bibliography_checked": True,
        "Dirac_current_bilinear_declared": True,
        "spinor_intertwiner_condition_declared": True,
        "Clifford_intertwining_condition_declared": True,
        "Dirac_adjoint_compatibility_declared": True,
        "observational_fit_forbidden": True,
    }
    algebraic_conditions = {
        "current_bilinear_formula_ready": True,
        "intertwiner_implies_gamma_transport_formula_ready": True,
        "intertwiner_implies_current_transport_conditional": True,
    }
    closure = {
        "plus_minus_spinor_bundle_data_ready": spinor_bundle[
            "plus_minus_spinor_bundle_data_ready"
        ],
        "local_Z2_spinor_intertwiner_on_Sigma_ready": local_intertwiner[
            "local_pin_reflection_intertwiner_ready"
        ],
        "Z2_spinor_intertwiner_from_resolved_tunnel_Pin_lift_ready": False,
        "Clifford_intertwining_verified": local_intertwiner["closure"][
            "local_Clifford_intertwiner_ready"
        ],
        "Dirac_adjoint_compatibility_verified": local_intertwiner["closure"][
            "Dirac_adjoint_local_compatibility_ready"
        ],
        "physical_spinor_equivariance_from_boundary_variation_ready": soldering_equivariance[
            "physical_spinor_equivariance_from_boundary_variation_ready"
        ],
        "physical_spinor_equivariance_from_quotient_descent_ready": quotient_descent_equivariance[
            "physical_spinor_equivariance_from_quotient_descent_ready"
        ],
        "physical_spinor_equivariance_derived": physical_equivariance_ready,
        "Dirac_current_Z2_parity_derived": False,
    }
    ready = all(declared.values()) and all(algebraic_conditions.values()) and all(closure.values())
    return {
        "status": "janus-z2-sigma-dirac-current-parity-from-spinor-intertwiner-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Pin groups as Clifford lifts of orthogonal transformations",
            "Dirac current covariance under spin/Pin intertwiners",
            "active plus/minus spinor bundle data gate",
        ],
        "source_links": [
            "https://deferentialgeometry.org/papers/The%20Pin%20Groups%20in%20Physics-%20C%2C%20P%2C%20and%20T.pdf",
            "https://hal.science/hal-00502337/document",
        ],
        "bibliography_result": (
            "Generic Pin/Clifford theory gives the conditional algebra: if the "
            "resolved-tunnel spinor lift intertwines gamma matrices and Dirac adjoints, "
            "then the vector current transports with the deck transformation. The active "
            "Janus proof still needs that resolved-tunnel intertwiner."
        ),
        "declared": declared,
        "algebraic_conditions": algebraic_conditions,
        "closure": closure,
        "upstream_frontiers": {
            "plus_minus_spinor_bundle_data": {
                "gate": spinor_bundle["status"],
                "ready": spinor_bundle["plus_minus_spinor_bundle_data_ready"],
                "primary_blocker": spinor_bundle["nearest_spinor_bundle_frontier"]["block"],
                "closure": spinor_bundle["closure"],
            },
            "local_pin_reflection_intertwiner": {
                "gate": local_intertwiner["status"],
                "ready": local_intertwiner["local_pin_reflection_intertwiner_ready"],
                "scope": local_intertwiner["scope"],
            },
            "spinor_soldering_equivariance": {
                "gate": soldering_equivariance["status"],
                "ready": soldering_equivariance[
                    "physical_spinor_equivariance_from_boundary_variation_ready"
                ],
                "primary_blocker": soldering_equivariance["primary_blocker"],
                "closure": soldering_equivariance["closure"],
            },
            "spinor_quotient_descent_equivariance": {
                "gate": quotient_descent_equivariance["status"],
                "ready": quotient_descent_equivariance[
                    "physical_spinor_equivariance_from_quotient_descent_ready"
                ],
                "primary_blocker": quotient_descent_equivariance["primary_blocker"],
                "closure": quotient_descent_equivariance["closure"],
            },
        },
        "formulas": {
            "dirac_current": "J^mu = psibar gamma^mu psi",
            "spinor_intertwiner": "psi_- = U_Z2 psi_+",
            "local_intertwiner": "U_Z2^Sigma = B_n is available locally on Sigma",
            "clifford_intertwining": "U_Z2^-1 gamma_-^mu U_Z2 = tau_Z2* gamma_+^mu",
            "adjoint_compatibility": "psibar_- = psibar_+ U_Z2^-1 with the active Dirac adjoint convention",
            "current_parity": "J_- = tau_Z2* J_+ once the intertwiner and adjoint compatibility are verified",
        },
        "conditional_current_parity_algebra_ready": all(declared.values())
        and all(algebraic_conditions.values()),
        "dirac_current_z2_parity_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "none"
        if ready
        else (
            "spinor_equivariance_routes_open"
            if local_intertwiner["local_pin_reflection_intertwiner_ready"]
            else "local_Z2_spinor_intertwiner_on_Sigma"
        ),
        "equivariance_route_blockers": []
        if physical_equivariance_ready
        else [
            soldering_equivariance["primary_blocker"],
            quotient_descent_equivariance["primary_blocker"],
        ],
        "next_required": []
        if ready
        else [
            "extend_local_U_Z2_to_resolved_tunnel_Pin_lift",
            "derive_plus_minus_spinor_bundle_data_on_resolved_tunnel",
            "close_spinor_soldering_boundary_variation_residual",
            "or_close_spinor_quotient_descent_equivariance",
            "then_promote_Dirac_current_Z2_parity",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Current Parity From Spinor Intertwiner Gate",
        "",
        f"Conditional algebra ready: `{payload['conditional_current_parity_algebra_ready']}`",
        f"Parity ready: `{payload['dirac_current_z2_parity_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

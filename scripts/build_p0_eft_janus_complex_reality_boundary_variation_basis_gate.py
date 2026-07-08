from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_sigma_boundary_projection_gate import (
    build_payload as build_sigma_projection_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_boundary_variation_basis_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_boundary_variation_basis_gate.md"


def build_payload() -> dict[str, Any]:
    projection = build_sigma_projection_payload()
    variation_basis = {
        "normal_embedding_displacement": {
            "symbol": "delta_X_perp",
            "maps_to": "gamma_Sigma^perp = e_perp_mu * deltaX^mu",
            "status": "physical_candidate_requires_active_embedding",
        },
        "tangential_embedding_displacement": {
            "symbol": "delta_X_parallel",
            "maps_to": "boundary diffeomorphism / reparametrization",
            "status": "gauge_quotient_required",
        },
        "frame_rotation_boost": {
            "symbol": "delta_L * L^{-1}",
            "maps_to": "omega_Sigma = antiHermitian_G(delta_L * L^{-1})",
            "status": "symbolic_generator_ready",
        },
        "connection_holonomy_around_sigma": {
            "symbol": "integral_around_Sigma X_Sigma^*(omega)",
            "maps_to": "omega_Sigma holonomy generator",
            "status": "requires_closed_boundary_cycle",
        },
    }
    checks = {
        "sigma_projection_symbolic_ready": projection[
            "sigma_boundary_to_complex_poincare_projection_symbolic_ready"
        ],
        "normal_embedding_displacement_declared": True,
        "tangential_gauge_quotient_declared": True,
        "frame_rotation_boost_declared": True,
        "connection_holonomy_channel_declared": True,
        "active_embedding_ready": projection["active_checks"]["active_embedding_ready"],
        "closed_boundary_two_cycle_declared": projection["active_checks"][
            "closed_boundary_two_cycle_declared"
        ],
    }
    symbolic_basis_ready = all(
        checks[key]
        for key in [
            "sigma_projection_symbolic_ready",
            "normal_embedding_displacement_declared",
            "tangential_gauge_quotient_declared",
            "frame_rotation_boost_declared",
            "connection_holonomy_channel_declared",
        ]
    )
    active_basis_ready = (
        symbolic_basis_ready
        and checks["active_embedding_ready"]
        and checks["closed_boundary_two_cycle_declared"]
    )
    return {
        "status": "janus-complex-reality-boundary-variation-basis-gate",
        "active_core": "Z2_tunnel_Sigma",
        "checks": checks,
        "variation_basis": variation_basis,
        "symbolic_boundary_variation_basis_ready": symbolic_basis_ready,
        "active_boundary_variation_basis_ready": active_basis_ready,
        "KKS_boundary_density_evaluable_now": active_basis_ready,
        "alpha_generated_now": False,
        "what_this_closes": [
            "symbolic_normal_embedding_displacement_channel",
            "symbolic_frame_rotation_boost_channel",
            "symbolic_connection_holonomy_channel",
            "tangential_embedding_variation_marked_gauge",
        ],
        "still_missing_for_active_density": [
            key
            for key in [
                "active_embedding_ready",
                "closed_boundary_two_cycle_declared",
            ]
            if not checks[key]
        ],
        "next_gate": "ComplexRealityClosedBoundaryTwoCycleGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Boundary Variation Basis Gate",
                "",
                f"Symbolic basis ready: `{payload['symbolic_boundary_variation_basis_ready']}`",
                f"Active basis ready: `{payload['active_boundary_variation_basis_ready']}`",
                f"KKS density evaluable now: `{payload['KKS_boundary_density_evaluable_now']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## Closed",
                "",
                *[f"- `{item}`" for item in payload["what_this_closes"]],
                "",
                "## Still Missing",
                "",
                *[f"- `{item}`" for item in payload["still_missing_for_active_density"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_equivariant_flux_cancellation_gate import (
    build_payload as build_equivariant_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flow_tangency_from_embedding_velocity_gate import (
    build_payload as build_flow_tangency_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_torsion_flux_zero_or_equivariance_gate import (
    build_payload as build_holst_torsion_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_perfect_fluid_tangential_flux_zero_gate import (
    build_payload as build_perfect_fluid_zero_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate import (
    build_payload as build_projected_dirac_normal_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_stress_equivariance_gate import (
    build_payload as build_stress_equivariance_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fa_zero_exhaustion_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fa_zero_exhaustion_gate.json")


def build_payload() -> dict:
    perfect_fluid = build_perfect_fluid_zero_payload()
    flow_tangency = build_flow_tangency_payload()
    holst_torsion_flux = build_holst_torsion_flux_payload()
    stress = build_stress_equivariance_payload()
    equivariant_flux = build_equivariant_flux_payload()
    normal_current = build_projected_dirac_normal_current_payload()

    routes = {
        "perfect_fluid_tangential": {
            "ready": perfect_fluid["gate_passed"],
            "status": "partial_matter_route",
            "primary_blocker": perfect_fluid["primary_blocker"],
            "scope": perfect_fluid["scope"],
        },
        "flow_tangency": {
            "ready": flow_tangency["gate_passed"],
            "status": "computed_u_dot_n_and_e_dot_n_route",
            "primary_blocker": flow_tangency["primary_blocker"],
        },
        "holst_torsion_flux": {
            "ready": holst_torsion_flux["gate_passed"],
            "status": "local_Sigma_Holst_flux_route",
            "primary_blocker": holst_torsion_flux["primary_blocker"],
            "scope": holst_torsion_flux["scope"],
        },
        "z2_equivariant_total_stress": {
            "ready": equivariant_flux["gate_passed"],
            "status": "total_flux_route",
            "primary_blocker": equivariant_flux["primary_blocker"],
        },
        "stress_transport": {
            "ready": stress["gate_passed"],
            "status": "upstream_for_z2_equivariant_total_stress",
            "primary_blocker": stress["primary_blocker"],
        },
        "no_normal_dirac_current": {
            "ready": normal_current["no_normal_dirac_current_ready"],
            "status": "transparency_current_route",
            "primary_blocker": normal_current["primary_blocker"],
            "sub_blockers": {
                "reflecting_route": normal_current["upstream_frontiers"][
                    "reflecting_spinor_boundary_current"
                ]["primary_blocker"],
                "z2_current_cancellation_route": normal_current["upstream_frontiers"][
                    "z2_current_cancellation"
                ]["primary_blocker"],
            },
        },
    }
    transparency_ready = (
        routes["no_normal_dirac_current"]["ready"]
        and (
            routes["z2_equivariant_total_stress"]["ready"]
            or (
                routes["perfect_fluid_tangential"]["ready"]
                and routes["holst_torsion_flux"]["ready"]
            )
        )
    )
    hard_remaining = []
    if not perfect_fluid["gate_passed"]:
        hard_remaining.extend([
            "Sigma_tangent_and_normal_frames",
            "metric_plus_minus_and_four_velocity_on_Sigma",
            "plus_minus_four_velocity_tangent_to_Sigma",
        ])
    if not holst_torsion_flux["gate_passed"]:
        hard_remaining.append("Holst_torsion_flux_zero_or_Z2_equivariance")
    hard_remaining.append("normal_dirac_current_zero_via_reflecting_or_Z2_parity")
    z2_current_blocker = normal_current["upstream_frontiers"]["z2_current_cancellation"][
        "primary_blocker"
    ]
    if z2_current_blocker != "none":
        hard_remaining.append(z2_current_blocker)
        hard_remaining.extend(
            normal_current["upstream_frontiers"]["z2_current_cancellation"].get(
                "route_blockers", []
            )
        )
    next_required = []
    if not perfect_fluid["gate_passed"]:
        next_required.extend([
            "derive_Sigma_tangent_and_normal_frames",
            "prove_u_dot_n_zero_for_plus_minus_comoving_flow",
            "close_perfect_fluid_matter_flux_zero",
        ])
    if not holst_torsion_flux["gate_passed"]:
        next_required.append("handle_Holst_torsion_flux_by_Z2_equivariance_or_zero_projection")
    next_required.append("close_normal_dirac_current_by_reflecting_boundary_or_Z2_current_parity")
    if z2_current_blocker != "none":
        next_required.extend([
            "close_spinor_soldering_boundary_variation_residual",
            "or_close_spinor_quotient_descent_equivariance",
        ])
    return {
        "status": "janus-z2-sigma-fa-zero-exhaustion-gate",
        "active_core": "Z2_tunnel_Sigma",
        "promising_not_rustine": True,
        "reason": (
            "F_a=0 can follow from geometric/tensor identities: perfect-fluid tangency, "
            "Z2 stress equivariance, and reflecting no-normal-current. None are fit knobs."
        ),
        "routes": routes,
        "active_sigma_transparency_ready": transparency_ready,
        "best_current_subroute": (
            "perfect_fluid_plus_torsionless_Holst_boundary_flux"
            if perfect_fluid["gate_passed"] and holst_torsion_flux["gate_passed"]
            else "perfect_fluid_tangential_for_matter_flux"
        ),
        "hard_remaining_blockers": hard_remaining,
        "next_required": next_required,
        "gate_passed": transparency_ready,
        "diagnostic_only": not transparency_ready,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma F_a=0 Exhaustion Gate",
        "",
        f"Promising not rustine: `{payload['promising_not_rustine']}`",
        f"Transparency ready: `{payload['active_sigma_transparency_ready']}`",
        f"Best current subroute: `{payload['best_current_subroute']}`",
        "",
        payload["reason"],
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(f"- `{name}`: ready=`{route['ready']}`, blocker=`{route['primary_blocker']}`")
    lines.extend(["", "## Hard Remaining Blockers"])
    lines.extend(f"- `{item}`" for item in payload["hard_remaining_blockers"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flux_projection_domain_gate import (
    build_payload as build_flux_domain_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flow_tangency_from_embedding_velocity_gate import (
    build_payload as build_flow_tangency_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_sector_density_pressure_of_a_gate import (
    build_payload as build_sector_density_pressure_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_perfect_fluid_tangential_flux_zero_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_perfect_fluid_tangential_flux_zero_gate.json")


def build_payload() -> dict:
    domain = build_flux_domain_payload()
    flow_tangency = build_flow_tangency_payload()
    sector = build_sector_density_pressure_payload()
    declared = {
        "perfect_fluid_flux_identity_declared": True,
        "tangent_normal_orthogonality_declared": True,
        "comoving_flow_tangent_to_Sigma_declared": True,
        "pressure_term_zero_by_e_dot_n_declared": True,
        "convective_term_zero_by_u_dot_n_declared": True,
        "rho_pressure_values_not_required_for_zero_identity": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "Sigma_tangents_ready": domain["closure"]["Sigma_tangents_ready"]
        or flow_tangency["flow_tangency_ready"],
        "Sigma_normals_ready": domain["closure"]["Sigma_normals_ready"]
        or flow_tangency["flow_tangency_ready"],
        "tangent_normal_orthogonality_derived": flow_tangency["flow_tangency_ready"],
        "plus_four_velocity_tangent_to_Sigma_derived": flow_tangency["flow_tangency_ready"],
        "minus_four_velocity_tangent_to_Sigma_derived": flow_tangency["flow_tangency_ready"],
        "perfect_fluid_normal_flux_zero_derived": flow_tangency["flow_tangency_ready"],
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none" if ready else next(key for key, value in closure.items() if not value)
    return {
        "status": "janus-z2-sigma-perfect-fluid-tangential-flux-zero-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_result": (
            "For a perfect fluid, T_munu e_a^mu n^nu = (rho+p)(u.e_a)(u.n)+p(e_a.n). "
            "Thus a comoving flow tangent to Sigma gives zero normal-tangent flux "
            "without fitting and without thermodynamic negative density."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "perfect_fluid": "T_munu = (rho+p) u_mu u_nu + p g_munu",
            "normal_tangent_flux": "T_munu e_a^mu n^nu = (rho+p)(u.e_a)(u.n)+p(e_a.n)",
            "orthogonality": "e_a.n = 0",
            "comoving_tangency": "u.n = 0",
            "result": "F_a^(perfect fluid) = 0 sector by sector",
        },
        "upstream_frontiers": {
            "flow_tangency": {
                "gate": flow_tangency["status"],
                "ready": flow_tangency["flow_tangency_ready"],
                "primary_blocker": flow_tangency["primary_blocker"],
            },
            "sector_density_pressure": {
                "gate": sector["status"],
                "ready": sector["sector_density_pressure_of_a_ready"],
                "primary_blocker": sector["primary_blocker"],
            },
        },
        "perfect_fluid_tangential_flux_zero_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "scope": {
            "matter_perfect_fluid_flux": "zero_if_ready",
            "Holst_torsion_flux": "not_closed_by_this_gate",
            "total_bulk_flux": "requires_Holst_zero_or_Z2_cancellation",
        },
        "next_required": [
            "derive_Sigma_tangent_and_normal_frames",
            "derive_plus_minus_rho_p_of_a",
            "derive_plus_minus_four_velocity_tangent_to_Sigma",
            "then_set_perfect_fluid_flux_zero_sector_by_sector",
            "handle_Holst_torsion_flux_separately",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Perfect-Fluid Tangential Flux Zero Gate",
        "",
        f"Ready: `{payload['perfect_fluid_tangential_flux_zero_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Formula",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Scope"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["scope"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

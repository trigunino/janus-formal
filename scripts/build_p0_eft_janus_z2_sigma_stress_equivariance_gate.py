from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_holst_torsion_stress_of_a_gate import (
    build_payload as build_holst_torsion_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_sector_density_pressure_of_a_gate import (
    build_payload as build_sector_density_pressure_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_stress_equivariance_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_stress_equivariance_gate.json")


def build_payload() -> dict:
    sector = build_sector_density_pressure_payload()
    holst = build_holst_torsion_payload()
    declared = {
        "Janus_Z2_stress_transport_declared": True,
        "perfect_fluid_stress_transport_declared": True,
        "Holst_torsion_stress_transport_declared": True,
        "thermodynamic_density_not_signed_by_hand": True,
        "gravitational_Z2_sign_policy_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_rho_p_of_a_ready": sector["closure"]["plus_rho_p_of_a_ready"],
        "minus_rho_p_of_a_ready": sector["closure"]["minus_rho_p_of_a_ready"],
        "rho_pressure_Z2_transport_derived": False,
        "four_velocity_Z2_transport_derived": False,
        "metric_Z2_transport_derived": False,
        "matter_stress_Z2_equivariance_derived": False,
        "Holst_torsion_stress_of_a_ready": holst["holst_torsion_stress_of_a_ready"],
        "Holst_torsion_stress_Z2_equivariance_derived": False,
        "total_stress_Z2_equivariance_derived": False,
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none" if ready else next(key for key, value in closure.items() if not value)
    return {
        "status": "janus-z2-sigma-stress-equivariance-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_result": (
            "A tensor stress transports naturally under a diffeomorphism, but the active "
            "Janus claim T_- = tau_* T_+ also requires sector rho/p, four-velocity, "
            "metric, and Holst/torsion stress to be Z2-related rather than fitted."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "perfect_fluid": "T_munu = (rho+p) u_mu u_nu + p g_munu",
            "matter_transport": "T_matter^- = tau_* T_matter^+ if rho/p, u, and g transport by tau_Z2",
            "holst_transport": "T_Holst^- = tau_* T_Holst^+ if torsion/Immirzi boundary data transport by tau_Z2",
            "total_transport": "T_total^- = tau_* T_total^+",
            "sign_policy": "Z2 gravitational sign is projection/orientation; rho_- is not set negative by hand",
        },
        "upstream_frontiers": {
            "sector_density_pressure": {
                "gate": sector["status"],
                "ready": sector["sector_density_pressure_of_a_ready"],
                "primary_blocker": sector["primary_blocker"],
            },
            "holst_torsion_stress": {
                "gate": holst["status"],
                "ready": holst["holst_torsion_stress_of_a_ready"],
                "primary_blocker": holst["primary_blocker"],
            },
        },
        "stress_equivariance_ledger_declared": all(declared.values()),
        "stress_equivariance_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "derive_rho_pressure_Z2_transport",
            "derive_four_velocity_Z2_transport",
            "derive_metric_Z2_transport",
            "derive_matter_stress_Z2_equivariance",
            "derive_Holst_torsion_stress_Z2_equivariance",
            "feed_total_stress_equivariance_to_flux_cancellation_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Stress Equivariance Gate",
        "",
        f"Ready: `{payload['stress_equivariance_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Formula",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

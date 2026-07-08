from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_bimetric_bulk_to_throat_mass_candidate_gate import (
    build_payload as build_bulk_to_throat_mass,
)
from scripts.build_p0_eft_janus_z2_exact_solution_alpha_state_sector_gate import (
    build_payload as build_alpha_state,
)
from scripts.build_p0_eft_janus_z2_exact_solution_alpha_to_global_energy_gate import (
    build_payload as build_alpha_to_energy,
)
from scripts.build_p0_eft_janus_z2_global_mass_state_from_exact_global_energy_volume_gate import (
    build_payload as build_energy_volume_to_mass,
)
from scripts.build_p0_eft_janus_z2_published_global_energy_constant_route_gate import (
    build_payload as build_energy_route,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate import (
    build_payload as build_volume_gate,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_to_throat_mass_chain.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_to_throat_mass_chain.json")


def build_payload() -> dict:
    alpha_state = build_alpha_state(write_output=True)
    alpha_to_energy = build_alpha_to_energy(write_output=True)
    energy_route = build_energy_route(write_output=True)
    volume_gate = build_volume_gate()
    energy_volume_to_mass = build_energy_volume_to_mass(write_output=True)
    bulk_to_throat = build_bulk_to_throat_mass(write_output=True)

    stages = {
        "alpha_state_sector": {
            "ready": alpha_state["gate_passed"],
            "blocker": alpha_state["remaining_blocker"],
        },
        "alpha_to_global_energy": {
            "ready": alpha_to_energy["gate_passed"],
            "blocker": alpha_to_energy["remaining_blocker"],
        },
        "global_energy_to_sector_density": {
            "ready": energy_route["gate_passed"],
            "blocker": (
                energy_route["validation_errors"][0]
                if energy_route["validation_errors"]
                else "none"
            ),
        },
        "spatial_volume_normalization": {
            "ready": volume_gate["gate_passed"],
            "blocker": volume_gate["primary_blocker"],
        },
        "global_mass_state_from_energy_volume": {
            "ready": energy_volume_to_mass["gate_passed"],
            "blocker": energy_volume_to_mass["primary_blocker"],
        },
        "strict_bulk_to_throat_mass": {
            "ready": bulk_to_throat["strict_throat_mass_ready"],
            "blocker": bulk_to_throat["primary_blocker"],
        },
    }

    first_blocker = "none"
    for stage in stages.values():
        if not stage["ready"]:
            first_blocker = stage["blocker"]
            break

    return {
        "status": "janus-z2-alpha-to-throat-mass-chain",
        "active_core": "Z2_tunnel_Sigma",
        "route": "alpha_m -> E_global -> rho_plus -> M_plus -> Sigma/PT projection -> M_bridge",
        "stages": stages,
        "strict_throat_mass_ready": bulk_to_throat["strict_throat_mass_ready"],
        "M_bridge_kg": bulk_to_throat["M_bridge_kg"],
        "first_blocker": first_blocker,
        "interpretation": (
            "This chain is the clean no-rustine route from a global Janus state sector "
            "to a throat mass. It closes only if alpha is supplied or derived, the exact "
            "global energy is materialized, an active spatial volume is available, and "
            "the Sigma/PT projection is proved."
        ),
        "next_required": bulk_to_throat["next_required"]
        if not bulk_to_throat["strict_throat_mass_ready"]
        else [],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha To Throat Mass Chain",
        "",
        f"Route: `{payload['route']}`",
        f"Strict throat mass ready: `{payload['strict_throat_mass_ready']}`",
        f"First blocker: `{payload['first_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Stages",
    ]
    for name, stage in payload["stages"].items():
        lines.append(f"- `{name}` ready=`{stage['ready']}` blocker=`{stage['blocker']}`")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

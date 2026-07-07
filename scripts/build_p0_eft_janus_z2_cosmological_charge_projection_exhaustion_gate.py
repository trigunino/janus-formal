from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_cosmological_total_charge_to_bridge_gate import (
    build_payload as build_total_charge_bridge,
)
from scripts.derive_p0_eft_janus_z2_sigma_no_extension_charge_normalization_no_go_gate import (
    build_payload as build_charge_no_go,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_cosmological_charge_projection_exhaustion_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_cosmological_charge_projection_exhaustion_gate.json"
)


def build_payload() -> dict:
    charge_no_go = build_charge_no_go()
    bridge = build_total_charge_bridge()
    channels = {
        "baryon_number_or_occupation": {
            "conserved": True,
            "absolute_value_selected": False,
            "projects_to_sigma_conditionally": True,
            "reason": (
                "Noether conservation preserves N after initial data are supplied, "
                "but Z2/topology does not select absolute N_occ."
            ),
        },
        "stress_energy_total_mass": {
            "conserved": "definition_dependent",
            "absolute_value_selected": bridge["global_mass_ready"],
            "projects_to_sigma_conditionally": bridge["projection_ready"],
            "reason": (
                "A closed cosmology lacks a canonical ADM mass; a quasilocal or "
                "Hamiltonian charge must be chosen and evaluated."
            ),
        },
        "bridge_quasilocal_mass": {
            "conserved": "if_Q_Sigma_equals_M_bridge_c2_is_proved",
            "absolute_value_selected": bridge["bridge_mass_ready"],
            "projects_to_sigma_conditionally": True,
            "reason": (
                "The null/PT throat can carry M_bridge, but the equality with "
                "the full visible-sector charge is an extra projection theorem."
            ),
        },
    }
    exhausted = (
        charge_no_go["consequence"]["no_extension_route_exhausted_at_charge_normalization"]
        and not bridge["gate_passed"]
    )
    return {
        "status": "janus-z2-cosmological-charge-projection-exhaustion-gate",
        "active_core": "Z2_tunnel_Sigma",
        "question": (
            "Can the total visible-sector charge be proved to become M_bridge "
            "at Sigma/PT with current no-extension data?"
        ),
        "channels": channels,
        "charge_no_go_primary_blocker": charge_no_go["primary_blocker"],
        "bridge_gate_passed": bridge["gate_passed"],
        "current_no_extension_projection_route_exhausted": exhausted,
        "intuition_status": (
            "physically_plausible_but_requires_state_or_projection_theorem"
        ),
        "minimal_missing_theorems": [
            "absolute_N_occ_or_global_mass_state_selection",
            "active_spatial_volume_or_quasilocal_surface_measure",
            "Sigma_PT_projection_completeness",
            "Q_Sigma_equals_M_bridge_c2",
        ],
        "best_next_non_rustine_move": (
            "derive a projection theorem for a chosen quasilocal charge; if it "
            "still needs absolute N or volume, declare the route exhausted under "
            "strict no-extension"
        ),
        "gate_passed": exhausted,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Cosmological Charge Projection Exhaustion Gate",
        "",
        f"Route exhausted now: `{payload['current_no_extension_projection_route_exhausted']}`",
        f"Intuition status: `{payload['intuition_status']}`",
        "",
        "## Minimal Missing Theorems",
    ]
    lines.extend(f"- `{item}`" for item in payload["minimal_missing_theorems"])
    lines.extend(["", f"Best next move: {payload['best_next_non_rustine_move']}"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

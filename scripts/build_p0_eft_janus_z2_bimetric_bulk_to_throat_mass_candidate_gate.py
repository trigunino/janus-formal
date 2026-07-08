from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_cosmological_total_charge_to_bridge_gate import (
    build_payload as build_total_charge_to_bridge,
)
from scripts.build_p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate import (
    build_payload as build_global_mass_reducer,
)
from scripts.build_p0_eft_janus_z2_published_bimetric_sector_ratio_gate import (
    build_payload as build_ratio_gate,
)


BASE = Path("outputs/active_z2_sigma")
PROJECTION_PATH = BASE / "cosmological_charge_sigma_projection_inputs.json"
GLOBAL_MASS_INPUT_PATH = BASE / "global_bimetric_stress_energy_state_inputs.json"
GLOBAL_SOLUTION_PATH = BASE / "null_bridge_global_mass_solution_inputs.json"
MASS_CHARGE_PATH = BASE / "null_bridge_mass_charge_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_bimetric_bulk_to_throat_mass_candidate_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_bimetric_bulk_to_throat_mass_candidate_gate.json"
)


def _payload_mass(payload: dict[str, Any] | None) -> float | None:
    if not payload:
        return None
    value = payload.get("M_bridge_kg")
    return float(value) if isinstance(value, (int, float)) else None


def build_payload(
    *,
    projection_path: Path = PROJECTION_PATH,
    global_mass_input_path: Path = GLOBAL_MASS_INPUT_PATH,
    global_solution_path: Path = GLOBAL_SOLUTION_PATH,
    mass_charge_path: Path = MASS_CHARGE_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    ratio = build_ratio_gate(write_output=write_output)
    global_mass = build_global_mass_reducer(
        input_path=global_mass_input_path,
        output_path=global_solution_path,
        write_output=write_output,
    )
    projected_bridge = build_total_charge_to_bridge(
        projection_path=projection_path,
        global_mass_path=global_mass_input_path,
        global_solution_path=global_solution_path,
        mass_charge_path=mass_charge_path,
        write_output=write_output,
    )

    bulk_mass_payload = global_mass.get("global_mass_payload")
    bridge_payload = projected_bridge.get("bridge_payload")
    bulk_mass = float(bulk_mass_payload["M_plus_kg"]) if bulk_mass_payload else None
    throat_mass = _payload_mass(bridge_payload)

    strict_ready = bool(projected_bridge["gate_passed"])
    bulk_only_ready = bool(global_mass["gate_passed"])
    primary_blocker = (
        "none"
        if strict_ready
        else (
            "Sigma_PT_projection_not_proved"
            if bulk_only_ready
            else "absolute_global_bimetric_mass_state_missing"
        )
    )

    return {
        "status": "janus-z2-bimetric-bulk-to-throat-mass-candidate-gate",
        "active_core": "Z2_tunnel_Sigma",
        "published_relative_bimetric_structure_ready": ratio["relative_sector_ratio_ready"],
        "published_relative_sector_ratio": ratio["ratio_payload"]["rho_minus0_over_rho_plus0"],
        "published_visible_fraction": ratio["ratio_payload"]["published_visible_fraction"],
        "published_negative_mass_fraction_abs": ratio["ratio_payload"][
            "published_negative_mass_fraction_abs"
        ],
        "published_attached_discussion_interpretation": {
            "a_plus_over_a_minus_order": "about 1e2",
            "c_plus_over_c_minus_order": "about 1e3",
            "role": "relative two-sector kinematics/transport only",
            "fixes_absolute_bridge_mass": False,
        },
        "global_bulk_mass_route_ready": bulk_only_ready,
        "bulk_mass_payload": bulk_mass_payload,
        "bulk_mass_candidate_kg": bulk_mass,
        "sigma_pt_projection_route_ready": strict_ready,
        "throat_mass_payload": bridge_payload,
        "M_bridge_kg": throat_mass,
        "strict_throat_mass_ready": strict_ready,
        "mass_interpretation": {
            "relative_bimetric_ratios_alone_fix_mass": False,
            "bulk_state_can_fix_absolute_mass_scale": bulk_only_ready,
            "throat_mass_requires_sigma_pt_projection": True,
            "local_sigma_ode_alone_fixes_mass": False,
        },
        "route_statement": (
            "The published 5/95 split and the attached plus/minus kinematic ratios "
            "support a genuine two-sector Janus reading, but they do not by themselves "
            "fix an absolute throat mass. A strict throat mass exists only if an "
            "absolute global bimetric mass state is available and its projection to "
            "Sigma/PT is proved."
        ),
        "primary_blocker": primary_blocker,
        "next_required": []
        if strict_ready
        else (
            [
                "derive_or_supply_active_global_bimetric_stress_energy_state",
                "then_prove_Sigma_PT_projection_factor_and_QSigma_equals_Mbridge_c2",
            ]
            if not bulk_only_ready
            else [
                "prove_Sigma_PT_projection_factor_and_QSigma_equals_Mbridge_c2",
                "do_not_promote_bulk_mass_to_throat_mass_without_projection",
            ]
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Bimetric Bulk To Throat Mass Candidate Gate",
        "",
        payload["route_statement"],
        "",
        f"Published relative structure ready: `{payload['published_relative_bimetric_structure_ready']}`",
        f"Global bulk mass route ready: `{payload['global_bulk_mass_route_ready']}`",
        f"Sigma/PT projection route ready: `{payload['sigma_pt_projection_route_ready']}`",
        f"Strict throat mass ready: `{payload['strict_throat_mass_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

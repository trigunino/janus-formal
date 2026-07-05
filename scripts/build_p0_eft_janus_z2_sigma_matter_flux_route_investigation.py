from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_embedding_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_system_gate import (
    build_payload as build_coupled_system_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_projection_components_from_embedding_stress_gate import (
    build_payload as build_projection_components_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate import (
    build_payload as build_transparency_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_input_writer_gate import (
    build_payload as build_transparency_input_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_route_investigation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_route_investigation.json")


def _status_block(payload: dict, ready_key: str | None = None) -> dict:
    ready = bool(payload.get(ready_key, payload.get("gate_passed", False))) if ready_key else bool(payload.get("gate_passed", False))
    return {
        "gate": payload.get("status", "unknown"),
        "ready": ready,
        "primary_blocker": payload.get("primary_blocker", "unknown"),
        "next_required": payload.get("next_required", []),
    }


def build_payload() -> dict:
    transparency = build_transparency_payload()
    transparency_input = build_transparency_input_payload()
    coupled = build_coupled_system_payload()
    embedding = build_embedding_readiness_payload()
    projection = build_projection_components_payload()

    transparency_ready = bool(transparency["active_sigma_transparency_ready"])
    coupled_chain_materialized = bool(
        coupled["coupled_radius_flux_ledger_declared"]
        and projection["status"]
        and embedding["active_embedding_readiness_ledger_declared"]
    )
    coupled_solution_ready = bool(coupled["coupled_radius_flux_solution_ready"])

    preferred_route = (
        "transparency_Fa_zero"
        if transparency_ready
        else "coupled_RSigma_embedding_flux_closure"
    )
    recommendation = {
        "preferred_route": preferred_route,
        "reason": (
            "Active Sigma transparency is already proven, so use F_a=0."
            if transparency_ready
            else "Transparency is still unproven; the coupled route has the constructive calculator chain down to primitive Sigma inputs."
        ),
        "route_choice_by_fit_forbidden": True,
        "no_zero_flux_shortcut": not transparency_ready,
    }

    return {
        "status": "janus-z2-sigma-matter-flux-route-investigation",
        "active_core": "Z2_tunnel_Sigma",
        "investigated_routes": [
            "transparency_Fa_zero_from_Janus_Z2_geometry",
            "coupled_RSigma_embedding_flux_closure",
        ],
        "negative_mass_principle": {
            "negative_gravitational_sector_present": True,
            "gravitational_sign_is_Z2_projection_sign": True,
            "thermodynamic_negative_density_assumed": False,
            "thermodynamic_density_must_be_supplied_or_derived": True,
            "rho_eff_shortcut_forbidden": True,
        },
        "transparency_route": {
            **_status_block(transparency, "active_sigma_transparency_ready"),
            "input_writer": _status_block(transparency_input),
            "sufficient_condition": transparency["sufficient_condition"],
            "physical_status": (
                "proven_transparency"
                if transparency_ready
                else "blocked_until_no_normal_current_and_bulk_flux_cancellation_are_derived"
            ),
        },
        "coupled_route": {
            **_status_block(coupled, "coupled_radius_flux_solution_ready"),
            "system_ready": coupled["coupled_radius_flux_system_ready"],
            "solution_ready": coupled_solution_ready,
            "calculator_chain_materialized": coupled_chain_materialized,
            "embedding_readiness": _status_block(embedding, "active_embedding_readiness_ready"),
            "projection_components": _status_block(projection),
            "physical_status": (
                "solved"
                if coupled_solution_ready
                else "open_but_constructive_to_primitive_Sigma_inputs"
            ),
        },
        "recommendation": recommendation,
        "winner_for_next_work": preferred_route,
        "next_required": (
            [
                "write_matter_flux_transparency_inputs",
                "propagate_E_matterFlux_zero",
            ]
            if transparency_ready
            else [
                "derive_sector_metric_on_sigma_inputs",
                "derive_sector_time_direction_on_sigma_inputs",
                "derive_sector_density_pressure_on_sigma_inputs",
                "derive_active_tunnel_embedding_geometry_inputs",
                "derive_radial_variation_tangent_weights_inputs",
                "then_compute_F_a_and_E_matterFlux_without_fit",
            ]
        ),
        "gate_passed": False,
        "diagnostic_only": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Route Investigation",
        "",
        f"Winner for next work: `{payload['winner_for_next_work']}`",
        f"Diagnostic only: `{payload['diagnostic_only']}`",
        "",
        "## Negative Mass Principle",
    ]
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["negative_mass_principle"].items()
    )
    lines.extend(
        [
            "",
            "## Route Status",
            f"- `transparency`: `{payload['transparency_route']['physical_status']}`",
            f"- `coupled`: `{payload['coupled_route']['physical_status']}`",
            "",
            "## Recommendation",
            payload["recommendation"]["reason"],
            "",
            "## Next Required",
        ]
    )
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_active_projection_gate import (
    build_payload as build_active_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_route_decision_gate import (
    build_payload as build_route_decision_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate import (
    build_payload as build_transparency_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_perfect_fluid_tangency_gate import (
    build_payload as build_perfect_fluid_radial_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_radial_block_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_radial_block_gate.json")


def build_payload() -> dict:
    transparency = build_transparency_payload()
    active_projection = build_active_projection_payload()
    route_decision = build_route_decision_payload()
    perfect_fluid_radial = build_perfect_fluid_radial_payload()
    transparency_ready = transparency["active_sigma_transparency_ready"]
    active_flux_ready = active_projection["active_flux_projection_ready"]
    perfect_fluid_radial_ready = perfect_fluid_radial["gate_passed"]
    route_ready = route_decision["matter_flux_route_decision_ready"]
    declared = {
        "thin_shell_flux_bibliography_checked": True,
        "normal_tangent_flux_formula_ready": True,
        "radial_flux_variation_declared": True,
        "transparency_branch_declared": True,
        "perfect_fluid_tangential_zero_branch_declared": True,
        "matter_flux_route_decision_gate_declared": True,
        "transparency_gate_declared": True,
        "active_flux_projection_gate_declared": True,
        "active_bulk_stress_projection_required": True,
        "Z2_flux_orientation_declared": True,
        "observational_fit_forbidden": True,
        "E_matterFlux_block_declared": True,
    }
    closure = {
        "transparency_condition_derived": transparency_ready,
        "active_flux_of_a_ready": active_flux_ready,
        "perfect_fluid_tangential_radial_zero_ready": perfect_fluid_radial_ready,
        "matter_flux_route_decision_ready": route_ready,
        "E_matterFlux_radial_block_reduced": route_ready
        and (transparency_ready or active_flux_ready or perfect_fluid_radial_ready),
    }
    return {
        "status": "janus-z2-sigma-matter-flux-radial-block-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell surface conservation identity",
            "Poisson-Visser thin-shell wormhole momentum-flux conservation",
            "Dynamic thin-shell wormhole flux terms in surface Bianchi identities",
            "active matter-flux route decision gate",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies the normal-tangent flux term and the "
            "transparent-shell branch. It does not decide whether the active Janus "
            "tunnel throat is transparent or carries a nonzero projected matter flux."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "transparency": {
                "gate": transparency["status"],
                "ready": transparency_ready,
                "primary_blocker": transparency.get(
                    "primary_blocker", "matter_flux_transparency"
                ),
                "current_frontier": transparency["current_frontier"],
            },
            "active_projection": {
                "gate": active_projection["status"],
                "ready": active_flux_ready,
                "primary_blocker": active_projection.get(
                    "primary_blocker", "matter_flux_active_projection"
                ),
                "closure": active_projection["closure"],
            },
            "route_decision": {
                "gate": route_decision["status"],
                "ready": route_ready,
                "primary_blocker": route_decision.get(
                    "primary_blocker", "matter_flux_route_decision"
                ),
                "selected_route": route_decision["selected_route"],
            },
            "perfect_fluid_tangential_zero": {
                "gate": perfect_fluid_radial["status"],
                "ready": perfect_fluid_radial_ready,
                "active_sigma_transparency_claimed": perfect_fluid_radial[
                    "active_sigma_transparency_claimed"
                ],
            },
        },
        "formula": {
            "flux_one_form": "F_a^pm = T_munu^pm e_a^mu n_pm^nu",
            "radial_block": "E_matterFlux = delta_RSigma integral_Sigma F_tau^Z2Sigma or 0 under derived transparency",
            "transparency_branch": "E_matterFlux = 0 only if F_a^Z2Sigma = 0 is derived from active Sigma physics",
            "perfect_fluid_branch": "E_matterFlux = 0 for the perfect-fluid tangential matter sector; full Sigma transparency is not claimed",
        },
        "matter_flux_radial_ledger_declared": all(declared.values()),
        "matter_flux_radial_block_reduced": all(declared.values())
        and (
            closure["transparency_condition_derived"]
            or closure["active_flux_of_a_ready"]
            or closure["perfect_fluid_tangential_radial_zero_ready"]
        )
        and closure["matter_flux_route_decision_ready"]
        and closure["E_matterFlux_radial_block_reduced"],
        "gate_passed": all(declared.values())
        and (
            closure["transparency_condition_derived"]
            or closure["active_flux_of_a_ready"]
            or closure["perfect_fluid_tangential_radial_zero_ready"]
        )
        and closure["matter_flux_route_decision_ready"]
        and closure["E_matterFlux_radial_block_reduced"],
        "primary_blocker": (
            "none"
            if (
                all(declared.values())
                and (
                    closure["transparency_condition_derived"]
                    or closure["active_flux_of_a_ready"]
                    or closure["perfect_fluid_tangential_radial_zero_ready"]
                )
                and closure["matter_flux_route_decision_ready"]
                and closure["E_matterFlux_radial_block_reduced"]
            )
            else (
                transparency.get("primary_blocker", "matter_flux_transparency")
                if not transparency_ready
                else active_projection.get("primary_blocker", "matter_flux_active_projection")
                if not active_flux_ready
                else route_decision.get("primary_blocker", "matter_flux_route_decision")
                if not route_ready
                else "E_matterFlux_radial_block"
            )
        ),
        "next_required": [
            "pass_matter_flux_transparency_gate_or_reject_transparency",
            "pass_matter_flux_route_decision_gate",
            "pass_matter_flux_active_projection_gate_if_not_transparent",
            "evaluate_F_a_Z2Sigma_of_a",
            "reduce_E_matterFlux_radial_block",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Radial Block Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['matter_flux_radial_ledger_declared']}`",
        f"Block reduced: `{payload['matter_flux_radial_block_reduced']}`",
        "",
        "## Formula",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formula"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

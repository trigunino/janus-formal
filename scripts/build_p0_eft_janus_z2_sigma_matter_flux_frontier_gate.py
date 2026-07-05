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
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radius_acyclicity_gate import (
    build_payload as build_acyclicity_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radial_block_gate import (
    build_payload as build_radial_block_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_route_decision_gate import (
    build_payload as build_route_decision_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate import (
    build_payload as build_transparency_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_frontier_gate.json")


def build_payload() -> dict:
    transparency = build_transparency_payload()
    active_projection = build_active_projection_payload()
    acyclicity = build_acyclicity_payload()
    route_decision = build_route_decision_payload()
    radial_block = build_radial_block_payload()
    declared = {
        "route_decision_gate_imported": True,
        "transparency_gate_imported": True,
        "active_projection_gate_imported": True,
        "normal_matter_current_gate_imported": True,
        "bulk_stress_flux_cancellation_gate_imported": True,
        "matter_flux_radius_acyclicity_gate_imported_without_cycle": True,
        "matter_flux_radial_block_gate_imported": True,
        "thin_shell_flux_bibliography_checked": True,
        "no_fit_route_policy_declared": True,
        "transparency_criteria_declared": True,
    }
    paths = {
        "no_normal_matter_current_ready": transparency["closure"][
            "no_normal_matter_current_derived"
        ],
        "bulk_stress_cancellation_ready": transparency["closure"][
            "bulk_stress_normal_projection_zero_derived"
        ]
        or transparency["closure"]["Z2_flux_cancellation_derived"],
        "active_sigma_transparency_ready": transparency["active_sigma_transparency_ready"],
        "active_flux_projection_ready": active_projection["active_flux_projection_ready"],
        "route_decision_ready": route_decision["matter_flux_route_decision_ready"],
        "matter_flux_radial_block_reduced": radial_block["matter_flux_radial_block_reduced"],
        "matter_flux_radius_acyclic_route_ready": acyclicity[
            "matter_flux_radius_acyclic_route_ready"
        ],
    }
    nearest_matter_flux_route_frontier = {
        "route": "transparency",
        "gate": "P0EFTJanusZ2SigmaMatterFluxTransparencyGate",
        "reason": (
            "non-circular route: active projection requires X_+/-[R_Sigma], "
            "while transparency can reduce E_matterFlux without a fitted radius"
        ),
        "required": [
            "derive J_n^Z2Sigma = 0 from active projected currents",
            "derive bulk normal-stress zero projection or exact Z2 cancellation",
            "then pass route decision and reduce E_matterFlux",
        ],
        "diagnostic_only": True,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell surface conservation and momentum-flux term",
            "Poisson-Visser thin-shell wormhole flux branch",
            "Darmois-Israel hypersurface stress-balance literature",
        ],
        "source_links": [
            "https://link.springer.com/article/10.1007/BF02710419",
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
            "https://arxiv.org/abs/gr-qc/0201054",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies the normal momentum-flux slot. For active "
            "Janus Z2/Sigma, the block can reduce only through a derived transparency "
            "condition or an explicit active projection F_a^Z2Sigma(a)."
        ),
        "declared": declared,
        "paths": paths,
        "upstream_frontiers": {
            "transparency": {
                "gate": transparency["status"],
                "ready": transparency["active_sigma_transparency_ready"],
                "primary_blocker": transparency["primary_blocker"],
                "closure": transparency["closure"],
            },
            "active_projection": {
                "gate": active_projection["status"],
                "ready": active_projection["active_flux_projection_ready"],
                "primary_blocker": active_projection["primary_blocker"],
                "closure": active_projection["closure"],
            },
            "route_decision": {
                "gate": route_decision["status"],
                "ready": route_decision["matter_flux_route_decision_ready"],
                "primary_blocker": route_decision["primary_blocker"],
                "closure": route_decision["closure"],
            },
            "acyclicity": {
                "gate": acyclicity["status"],
                "ready": acyclicity["matter_flux_radius_acyclic_route_ready"],
                "closure": acyclicity["closure"],
                "current_frontier": acyclicity["current_frontier"],
                "policy": acyclicity["policy"],
            },
            "radial_block": {
                "gate": radial_block["status"],
                "ready": radial_block["matter_flux_radial_block_reduced"],
                "primary_blocker": radial_block["primary_blocker"],
                "closure": radial_block["closure"],
            },
        },
        "routes": {
            "transparency": "no_normal_matter_current + bulk_stress_Z2_cancellation -> E_matterFlux = 0",
            "active_projection": "T_pm(a), tangents, normals -> F_a^Z2Sigma(a) -> E_matterFlux(a)",
        },
        "current_frontier": [
            f"{key} = false"
            for key, ready in paths.items()
            if not ready
        ],
        "nearest_matter_flux_route_frontier": nearest_matter_flux_route_frontier,
        "nearest_matter_flux_route_frontier_declared": True,
        "nearest_matter_flux_route_frontier_diagnostic_only": True,
        "matter_flux_frontier_ledger_declared": all(declared.values()),
        "matter_flux_transparency_path_ready": all(declared.values())
        and paths["active_sigma_transparency_ready"],
        "matter_flux_active_projection_path_ready": all(declared.values())
        and paths["active_flux_projection_ready"],
        "matter_flux_frontier_ready": all(declared.values())
        and (
            paths["active_sigma_transparency_ready"]
            or paths["active_flux_projection_ready"]
        )
        and paths["matter_flux_radius_acyclic_route_ready"]
        and paths["route_decision_ready"]
        and paths["matter_flux_radial_block_reduced"],
        "primary_blocker": (
            "none"
            if (
                all(declared.values())
                and (
                    paths["active_sigma_transparency_ready"]
                    or paths["active_flux_projection_ready"]
                )
                and paths["matter_flux_radius_acyclic_route_ready"]
                and paths["route_decision_ready"]
                and paths["matter_flux_radial_block_reduced"]
            )
            else (
                transparency["primary_blocker"]
                if not paths["active_sigma_transparency_ready"]
                else active_projection["primary_blocker"]
                if not paths["active_flux_projection_ready"]
                else acyclicity["primary_blocker"]
                if not paths["matter_flux_radius_acyclic_route_ready"]
                else route_decision["primary_blocker"]
                if not paths["route_decision_ready"]
                else radial_block["primary_blocker"]
            )
        ),
        "next_required": [
            "close_normal_matter_current_gate_and_bulk_stress_flux_cancellation_for_transparency",
            "or_close_bulk_stress_of_a_and_embedding_for_active_projection",
            "pass_matter_flux_radius_acyclicity_gate",
            "then_pass_matter_flux_route_decision_gate",
            "then_reduce_E_matterFlux_radial_block",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Frontier Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['matter_flux_frontier_ledger_declared']}`",
        f"Transparency path ready: `{payload['matter_flux_transparency_path_ready']}`",
        f"Active projection path ready: `{payload['matter_flux_active_projection_path_ready']}`",
        f"Frontier ready: `{payload['matter_flux_frontier_ready']}`",
        "",
        "## Routes",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["routes"].items())
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Nearest Route Frontier"])
    nearest = payload["nearest_matter_flux_route_frontier"]
    lines.append(f"- `route`: `{nearest['route']}`")
    lines.append(f"- `gate`: `{nearest['gate']}`")
    lines.append(f"- `reason`: {nearest['reason']}")
    lines.extend(f"- `required`: `{item}`" for item in nearest["required"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

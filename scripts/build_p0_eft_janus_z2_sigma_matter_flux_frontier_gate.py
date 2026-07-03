from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_frontier_gate.json")


def build_payload() -> dict:
    declared = {
        "route_decision_gate_imported": True,
        "transparency_gate_imported": True,
        "active_projection_gate_imported": True,
        "normal_matter_current_gate_imported": True,
        "bulk_stress_flux_cancellation_gate_imported": True,
        "matter_flux_radius_acyclicity_gate_imported": True,
        "thin_shell_flux_bibliography_checked": True,
        "no_fit_route_policy_declared": True,
        "transparency_criteria_declared": True,
    }
    paths = {
        "no_normal_matter_current_ready": False,
        "bulk_stress_cancellation_ready": False,
        "active_flux_projection_ready": False,
        "matter_flux_radius_acyclic_route_ready": False,
        "route_decision_ready": False,
        "matter_flux_radial_block_reduced": False,
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
        "routes": {
            "transparency": "no_normal_matter_current + bulk_stress_Z2_cancellation -> E_matterFlux = 0",
            "active_projection": "T_pm(a), tangents, normals -> F_a^Z2Sigma(a) -> E_matterFlux(a)",
        },
        "current_frontier": [
            "no_normal_matter_current_ready = false",
            "bulk_stress_cancellation_ready = false",
            "active_flux_projection_ready = false",
            "matter_flux_radius_acyclic_route_ready = false",
        ],
        "matter_flux_frontier_ledger_declared": all(declared.values()),
        "matter_flux_transparency_path_ready": all(declared.values())
        and paths["no_normal_matter_current_ready"]
        and paths["bulk_stress_cancellation_ready"],
        "matter_flux_active_projection_path_ready": all(declared.values())
        and paths["active_flux_projection_ready"],
        "matter_flux_frontier_ready": all(declared.values())
        and (
            (
                paths["no_normal_matter_current_ready"]
                and paths["bulk_stress_cancellation_ready"]
            )
            or paths["active_flux_projection_ready"]
        )
        and paths["matter_flux_radius_acyclic_route_ready"]
        and paths["route_decision_ready"]
        and paths["matter_flux_radial_block_reduced"],
        "next_required": [
            "close_normal_matter_current_gate_and_bulk_stress_flux_cancellation_for_transparency",
            "or_close_bulk_stress_of_a_and_embedding_for_active_projection",
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
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

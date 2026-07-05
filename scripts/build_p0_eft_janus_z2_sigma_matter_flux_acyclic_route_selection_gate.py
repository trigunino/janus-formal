from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_system_gate import (
    build_payload as build_coupled_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radius_acyclicity_gate import (
    build_payload as build_acyclicity_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate import (
    build_payload as build_transparency_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_acyclic_route_selection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_acyclic_route_selection_gate.json")


def build_payload() -> dict:
    transparency = build_transparency_payload()
    acyclicity = build_acyclicity_payload()
    coupled = build_coupled_payload()
    transparency_depends_on_embedding = any(
        item in transparency["current_frontier"]
        for item in [
            "normal_matter_current_readiness_ready = false",
            "bulk_stress_normal_flux_projection_ready = false",
        ]
    )
    transparency_acyclic = bool(acyclicity["closure"]["transparency_acyclic_ready"])
    selected_route = (
        "transparency"
        if transparency_acyclic and transparency["active_sigma_transparency_ready"]
        else "coupled_radius_flux"
    )
    gate_passed = (
        selected_route == "transparency"
        and transparency_acyclic
        and transparency["active_sigma_transparency_ready"]
        and not transparency_depends_on_embedding
    ) or (
        selected_route == "coupled_radius_flux"
        and coupled["coupled_radius_flux_solution_ready"]
    )
    return {
        "status": "janus-z2-sigma-matter-flux-acyclic-route-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "transparency_gate": transparency["status"],
        "acyclicity_gate": acyclicity["status"],
        "coupled_gate": coupled["status"],
        "transparency_depends_on_unknown_embedding": transparency_depends_on_embedding,
        "transparency_acyclic_ready": transparency_acyclic,
        "active_sigma_transparency_ready": transparency["active_sigma_transparency_ready"],
        "coupled_radius_flux_system_ready": coupled["coupled_radius_flux_system_ready"],
        "coupled_radius_flux_solution_ready": coupled["coupled_radius_flux_solution_ready"],
        "selected_nonfit_route": selected_route,
        "independent_flux_shortcut_forbidden": True,
        "uses_observational_radius_fit": False,
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "gate_passed": gate_passed,
        "blocker": None
        if gate_passed
        else (
            "transparency is not independently acyclic; solve coupled R_Sigma/F_a "
            "system or derive embedding-independent transparency"
        ),
        "next_required": []
        if gate_passed
        else [
            "derive_transparency_without_unknown_embedding_or_RSigma",
            "or_close_coupled_radius_flux_function_space",
            "prove_coupled_radius_flux_well_posedness",
            "solve_coupled_RSigma_Flux_system_without_fit",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Acyclic Route Selection Gate",
        "",
        f"Selected route: `{payload['selected_nonfit_route']}`",
        f"Transparency depends on unknown embedding: `{payload['transparency_depends_on_unknown_embedding']}`",
        f"Transparency acyclic ready: `{payload['transparency_acyclic_ready']}`",
        f"Coupled solution ready: `{payload['coupled_radius_flux_solution_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["blocker"]:
        lines.extend(["", "## Blocker", payload["blocker"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

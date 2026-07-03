from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_radius_acyclicity_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_radius_acyclicity_gate.json")


def build_payload() -> dict:
    declared = {
        "matter_flux_frontier_imported": True,
        "coupled_radius_flux_system_imported": True,
        "active_embedding_from_radius_imported": True,
        "thin_shell_flux_bibliography_checked": True,
        "active_projection_uses_embedding_declared": True,
        "embedding_depends_on_RSigma_declared": True,
        "independent_flux_source_for_radius_forbidden": True,
        "transparency_may_be_acyclic_if_derived_independently": True,
        "coupled_radius_flux_route_declared": True,
    }
    closure = {
        "transparency_acyclic_ready": False,
        "active_projection_acyclic_ready": False,
        "coupled_radius_flux_system_ready": False,
        "matter_flux_can_enter_radius_solution": False,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-radius-acyclicity-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell conservation equation with external flux",
            "Poisson-Visser shell radius dynamics",
            "Mars-Senovilla hypersurface matching and shell geometry",
        ],
        "source_links": [
            "https://link.springer.com/article/10.1007/BF02710419",
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
            "https://arxiv.org/abs/gr-qc/0201054",
        ],
        "bibliography_result": (
            "A shell radius equation may include a normal flux source, but if that "
            "source is computed from active tangents/normals then it depends on the "
            "embedding and cannot be used as an independent input for R_Sigma(a)."
        ),
        "declared": declared,
        "closure": closure,
        "policy": {
            "forbidden": "use F_a^Z2Sigma[X_pm(R_Sigma)] as an already-known source for solving R_Sigma(a)",
            "allowed_transparency": "derive F_a^Z2Sigma=0 independently of the unknown embedding/radius",
            "allowed_coupled_route": "solve E_RSigma(a)=0 and F_a^Z2Sigma(a) as a coupled radius-flux system",
        },
        "current_frontier": [
            "transparency_acyclic_ready = false",
            "coupled_radius_flux_system_ready = false",
        ],
        "matter_flux_radius_acyclicity_ledger_declared": all(declared.values()),
        "matter_flux_radius_acyclic_route_ready": all(declared.values())
        and (closure["transparency_acyclic_ready"] or closure["coupled_radius_flux_system_ready"])
        and closure["matter_flux_can_enter_radius_solution"],
        "next_required": [
            "derive_transparency_without_using_unknown_X_pm_or_RSigma",
            "pass_coupled_radius_flux_system_gate",
            "then_allow_matter_flux_block_into_E_RSigma_solution_certificate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Radius Acyclicity Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['matter_flux_radius_acyclicity_ledger_declared']}`",
        f"Acyclic route ready: `{payload['matter_flux_radius_acyclic_route_ready']}`",
        "",
        "## Policy",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["policy"].items())
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

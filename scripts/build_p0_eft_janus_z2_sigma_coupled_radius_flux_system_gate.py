from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_function_space_gate import (
    build_payload as build_function_space_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_well_posedness_gate import (
    build_payload as build_well_posedness_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_system_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_system_gate.json")


def build_payload() -> dict:
    function_space = build_function_space_payload()
    well_posedness = build_well_posedness_payload()
    declared = {
        "throat_radius_variational_equation_imported": True,
        "matter_flux_active_projection_imported": True,
        "matter_flux_radius_acyclicity_imported": True,
        "coupled_radius_flux_function_space_imported": True,
        "coupled_radius_flux_well_posedness_imported": True,
        "thin_shell_flux_bibliography_checked": True,
        "coupled_unknowns_declared": True,
        "coupled_equations_declared": True,
        "no_independent_flux_shortcut_declared": True,
        "no_observational_radius_fit": True,
    }
    system = {
        "E_RSigma_equation_ready": True,
        "F_Z2Sigma_functional_declared": True,
        "embedding_dependence_recorded": True,
        "closure_conditions_declared": True,
        "function_space_ready_for_well_posedness": function_space["function_space_ready"],
        "well_posedness_ready": well_posedness["well_posedness_ready"],
        "coupled_system_well_posed": well_posedness["coupled_system_well_posed"],
    }
    solution = {
        "coupled_system_solved": False,
        "R_Sigma_of_a_ready": False,
        "active_flux_of_a_ready": False,
        "matter_flux_can_enter_radius_solution": False,
    }
    system_ready = all(declared.values()) and all(system.values())
    solution_ready = system_ready and all(solution.values())
    primary_blocker = (
        "none"
        if solution_ready
        else function_space.get("primary_blocker")
        or well_posedness.get("primary_blocker")
        or "function_space_and_well_posedness_before_solution"
    )
    return {
        "status": "janus-z2-sigma-coupled-radius-flux-system-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell conservation equation with external flux",
            "Poisson-Visser thin-shell throat dynamics",
            "Dynamic thin-shell flux/momentum conservation literature",
        ],
        "source_links": [
            "https://link.springer.com/article/10.1007/BF02710419",
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
            "https://link.aps.org/doi/10.1103/PhysRevD.101.124035",
            "https://cosmo.fis.fc.ul.pt/~crawford/papers/cqg204034p17.pdf",
        ],
        "bibliography_result": (
            "External flux is a standard shell-conservation source. In Janus Z2/Sigma, "
            "because F_a depends on X_pm[R_Sigma], the valid non-transparent route is "
            "a coupled radius-flux system, not a precomputed flux insertion."
        ),
        "declared": declared,
        "system": system,
        "solution": solution,
        "coupled_unknowns": [
            "R_Sigma(a)",
            "X_+/-[R_Sigma](a,xi)",
            "F_a^Z2Sigma(a)",
        ],
        "coupled_equations": {
            "radius": "E_RSigma[R_Sigma,F_a,counterterm,...](a)=0",
            "flux": "F_a^Z2Sigma(a)=T_pm(a;R_Sigma) e_a^mu[R_Sigma] n_mu[R_Sigma]",
            "embedding": "X_pm(a)=X_pm[R_Sigma](a) from conditional radius-to-embedding map",
        },
        "upstream_frontiers": {
            "function_space": {
                "gate": function_space["status"],
                "ready": function_space["function_space_ready"],
                "current_frontier": function_space["current_frontier"],
                "primary_blocker": function_space.get("primary_blocker"),
            },
            "well_posedness": {
                "gate": well_posedness["status"],
                "ready": well_posedness["well_posedness_ready"],
                "current_frontier": well_posedness["current_frontier"],
                "primary_blocker": well_posedness.get("primary_blocker"),
            },
        },
        "well_posedness_reduction_frontier": {
            "function_space_ready": function_space["function_space_ready"],
            "well_posedness_ready": well_posedness["well_posedness_ready"],
            "remaining_function_space_blockers": function_space["current_frontier"],
            "remaining_well_posedness_blockers": well_posedness["current_frontier"],
        },
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, ready in system.items()
            if not ready
        ]
        + [
            f"{key} = false"
            for key, ready in solution.items()
            if not ready
        ],
        "coupled_radius_flux_ledger_declared": all(declared.values()),
        "coupled_radius_flux_system_ready": system_ready,
        "coupled_radius_flux_solution_ready": solution_ready,
        "next_required": [
            "derive_closure_conditions_for_coupled_RSigma_Flux_system",
            "prove_well_posedness_or_reduce_to_transparency",
            "solve_coupled_system_without_observational_fit",
            "feed_solution_to_matter_flux_radius_acyclicity_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coupled Radius-Flux System Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['coupled_radius_flux_ledger_declared']}`",
        f"System ready: `{payload['coupled_radius_flux_system_ready']}`",
        f"Solution ready: `{payload['coupled_radius_flux_solution_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Coupled Equations",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["coupled_equations"].items())
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

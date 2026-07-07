from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
THETA_PATH = Path("outputs/active_z2_sigma/holst_palatini_boundary_theta_pt67_projection.json")
SOURIAU_PATH = REPORTS / "p0_eft_janus_z2_sigma_souriau_boundary_hamiltonian_attempt.json"
LLBRANE_PATH = REPORTS / "p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate.json"
SCOUPLE_PATH = REPORTS / "p0_scouple_accepted_action_search.json"
HARD_ROUTES_PATH = REPORTS / "p0_eft_janus_z2_alpha_two_hard_routes_gate.json"
JSON_PATH = REPORTS / "p0_eft_janus_z2_alpha_branch_archive_readiness_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_alpha_branch_archive_readiness_gate.md"


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values: Any) -> bool:
    return isinstance(values, list) and all(float(v) == 0.0 for v in values)


def build_payload(
    theta_path: Path = THETA_PATH,
    souriau_path: Path = SOURIAU_PATH,
    llbrane_path: Path = LLBRANE_PATH,
    scouple_path: Path = SCOUPLE_PATH,
    hard_routes_path: Path = HARD_ROUTES_PATH,
) -> dict[str, Any]:
    theta = _read(theta_path)
    souriau = _read(souriau_path)
    llbrane = _read(llbrane_path)
    scouple = _read(scouple_path)
    hard = _read(hard_routes_path)

    theta_ready = bool(theta.get("R_h_trace_values_ready")) and bool(
        theta.get("R_K_trace_values_ready")
    )
    theta_zero = theta_ready and _all_zero(theta.get("R_h_trace_values")) and _all_zero(
        theta.get("R_K_trace_values")
    )

    kks_density_ready = bool(souriau.get("local_density_from_charge_available")) or bool(
        souriau.get("metric_variation_available")
    )
    torsionful_or_null_theta_ready = (theta_ready and not theta_zero) or bool(
        llbrane.get("chi_LL_derivation_ready")
    )
    matter_gauge_phase_space_ready = bool(
        souriau.get("alpha_h_from_souriau_hamiltonian")
    ) or bool(souriau.get("alpha_K_from_souriau_hamiltonian"))
    published_minisuperspace_ready = bool(
        scouple.get("m15_action_accepted_for_field_equations")
    ) and bool(hard.get("valpha_route", {}).get("V_alpha_ready"))

    reopen_routes = {
        "nonzero_PT_KKS_Souriau_boundary_density": {
            "ready": kks_density_ready,
            "evidence": "Souriau report has no local density/metric variation"
            if not kks_density_ready
            else "local Souriau/KKS density available",
        },
        "torsionful_or_null_boundary_theta": {
            "ready": torsionful_or_null_theta_ready,
            "evidence": "PT67 theta is torsionless/zero and null LL branch lacks chi_LL selection"
            if not torsionful_or_null_theta_ready
            else "nonzero theta or LL chi selection available",
        },
        "matter_or_gauge_boundary_phase_space": {
            "ready": matter_gauge_phase_space_ready,
            "evidence": "no active matter/gauge Hamiltonian density coupled to h_ab/K_ab"
            if not matter_gauge_phase_space_ready
            else "matter/gauge boundary phase space available",
        },
        "published_minisuperspace_action_with_finite_noncompact_orbit_boundary": {
            "ready": published_minisuperspace_ready,
            "evidence": "M15/M30 field-equation action exists, but no on-shell V(alpha) and no finite u-boundary prescription"
            if not published_minisuperspace_ready
            else "V(alpha) selector ready",
        },
    }
    any_reopen_ready = any(route["ready"] for route in reopen_routes.values())

    return {
        "status": "janus-z2-alpha-branch-archive-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "alpha_global_state_selector",
        "current_classification": "continuous_global_energy_state_sector",
        "alpha_generated_no_fit": False,
        "published_janus_equivalence_on_alpha": True,
        "reopen_routes": reopen_routes,
        "any_reopen_route_ready": any_reopen_ready,
        "archive_branch_recommended": not any_reopen_ready,
        "archive_meaning": "archive as inactive/conditional, not delete; reopen only with one listed non-rustine input",
        "allowed_reopen_inputs": [
            "derive a nonzero PT KKS/Souriau boundary density",
            "derive torsionful/null boundary theta with a nonzero period and selected chi_LL",
            "derive matter/gauge boundary phase space on Sigma",
            "materialize the published bimetric minisuperspace action and finite boundary prescription for the noncompact exact orbit",
        ],
        "forbidden_shortcuts": [
            "do_not_fit_alpha_as_no_fit_prediction",
            "do_not_promote_continuous_alpha_sector_as_unique_selector",
            "do_not_treat_global_Souriau_charge_as_local_density_without_boundary_phase_space",
            "do_not_use_LL_brane_mass_relation_without_chi_LL_selection",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Alpha Branch Archive Readiness Gate",
                "",
                f"Classification: `{payload['current_classification']}`",
                f"Any reopen route ready: `{payload['any_reopen_route_ready']}`",
                f"Archive recommended: `{payload['archive_branch_recommended']}`",
                "",
                "This archives the alpha branch as conditional/inactive, not deleted.",
                "It can be reopened only by a non-rustine boundary density, torsionful/null theta, matter/gauge phase space, or a finite minisuperspace V(alpha) prescription.",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
HORIZON_PATH = REPORTS / "p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate.json"
NULL_BRANCH_PATH = REPORTS / "p0_eft_janus_z2_null_sigma_branch_verdict_gate.json"
LLBRANE_PATH = REPORTS / "p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate.json"
JSON_PATH = REPORTS / "p0_eft_janus_z2_null_pt_thermodynamic_alpha_selector_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_null_pt_thermodynamic_alpha_selector_gate.md"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    horizon_path: Path = HORIZON_PATH,
    null_branch_path: Path = NULL_BRANCH_PATH,
    llbrane_path: Path = LLBRANE_PATH,
) -> dict:
    horizon = _read(horizon_path)
    null_branch = _read(null_branch_path)
    llbrane = _read(llbrane_path)

    checks = horizon.get("checks", {})
    horizon_status = bool(checks.get("proved_horizon_status"))
    surface_gravity = bool(checks.get("kappa_l_available"))
    entropy_law = bool(checks.get("entropy_law_declared"))
    temperature_law = bool(checks.get("temperature_law_declared"))
    first_law_energy = bool(checks.get("first_law_energy_definition_available"))
    chi_selected = bool(llbrane.get("chi_LL_derivation_ready"))
    null_consistent = bool(
        null_branch.get("source_consistency_frontier", {}).get("chapter_6_3_eddington_surface")
    ) or bool(null_branch.get("branch") == "Z2_null_Sigma_PT_bridge")

    alpha_selector_ready = (
        null_consistent
        and horizon_status
        and surface_gravity
        and entropy_law
        and temperature_law
        and first_law_energy
        and chi_selected
    )

    return {
        "status": "janus-z2-null-pt-thermodynamic-alpha-selector-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "horizon_null_thermodynamics",
        "null_PT_bridge_context_available": null_consistent,
        "proved_horizon_status": horizon_status,
        "surface_gravity_kappa_available": surface_gravity,
        "entropy_law_declared": entropy_law,
        "temperature_law_declared": temperature_law,
        "first_law_energy_definition_available": first_law_energy,
        "chi_LL_selected": chi_selected,
        "alpha_selector_ready": alpha_selector_ready,
        "blocked_by": [
            name
            for name, ready in {
                "proved_horizon_status": horizon_status,
                "surface_gravity_kappa_available": surface_gravity,
                "entropy_law_declared": entropy_law,
                "temperature_law_declared": temperature_law,
                "first_law_energy_definition_available": first_law_energy,
                "chi_LL_selected": chi_selected,
            }.items()
            if not ready
        ],
        "bibliography_anchor": [
            "Cai-Kim apparent-horizon first law -> Friedmann",
            "Hayward unified first law",
            "Parattu-Padmanabhan null boundary term",
            "Chandrasekaran-Flanagan-Speranza null Brown-York charges",
        ],
        "interpretation": (
            "Null/horizon thermodynamics is a legitimate possible selector, but "
            "it is not active until the Janus/PT surface is proved to be the "
            "relevant horizon with kappa, entropy, temperature, first-law energy, "
            "and a selected chi_LL."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Null/PT Thermodynamic Alpha Selector Gate",
                "",
                f"Null/PT context: `{payload['null_PT_bridge_context_available']}`",
                f"Horizon status: `{payload['proved_horizon_status']}`",
                f"Surface gravity: `{payload['surface_gravity_kappa_available']}`",
                f"First-law energy: `{payload['first_law_energy_definition_available']}`",
                f"chi_LL selected: `{payload['chi_LL_selected']}`",
                f"Alpha selector ready: `{payload['alpha_selector_ready']}`",
                "",
                payload["interpretation"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

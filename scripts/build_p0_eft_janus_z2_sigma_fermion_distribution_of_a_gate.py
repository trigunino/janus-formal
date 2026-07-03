from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fermion_distribution_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fermion_distribution_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "fermion_distribution_bibliography_checked": True,
        "Dirac_gas_route_declared": True,
        "Weyssenhoff_fluid_route_declared": True,
        "particle_number_conservation_imported": True,
        "fermion_route_selection_gate_imported": True,
        "Dirac_number_density_gate_imported": True,
        "Dirac_mass_temperature_law_gate_imported": True,
        "Z2Sigma_projection_required": True,
        "thermodynamic_sign_policy_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "route_selected_from_action_or_topology": True,
        "fermion_number_density_of_a_ready": False,
        "fermion_mass_or_temperature_law_ready": False,
        "plus_fermion_distribution_of_a_ready": False,
        "minus_fermion_distribution_of_a_ready": False,
        "projected_fermion_distribution_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-fermion-distribution-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Hehl et al. 1976, Rev. Mod. Phys. 48, 393",
            "Obukhov/Korotky 1987, Class. Quantum Grav. 4, 1633",
            "de Berredo-Peixoto/de Freitas 2009, arXiv:0907.1701",
            "active Sigma spinor-variation route-selection gate",
            "Dirac fermion number-density gate",
            "Dirac mass/temperature law gate",
            "Einstein-Cartan-Dirac cosmology literature",
        ],
        "bibliography_result": (
            "Primary literature supplies generic Dirac-gas and Weyssenhoff-fluid "
            "routes, plus particle-number conservation machinery. It does not "
            "select the active Janus Z2/Sigma fermion distribution or its projected "
            "plus/minus histories as functions of a."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "number_conservation": "d(n_pm a^3)/d ln a = 0 only after the active fermion route is selected",
            "dirac_gas_route": "f_pm(a,p,s) determines axial current A_pm^mu(a)",
            "weyssenhoff_route": "spin-fluid density s_pm^2(a) derived from microscopic spin averaging",
            "projection": "f_Z2Sigma(a) = project_Z2Sigma(f_+(a), f_-(a))",
        },
        "fermion_distribution_ledger_declared": all(declared.values()),
        "fermion_distribution_of_a_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_fermion_number_density_of_a_gate",
            "pass_Dirac_mass_temperature_law_of_a_gate",
            "derive_plus_minus_fermion_distributions_of_a",
            "project_fermion_distribution_through_Z2Sigma_throat",
            "propagate_fermion_distribution_to_spin_current_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Fermion Distribution Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['fermion_distribution_ledger_declared']}`",
        f"Fermion distribution ready: `{payload['fermion_distribution_of_a_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

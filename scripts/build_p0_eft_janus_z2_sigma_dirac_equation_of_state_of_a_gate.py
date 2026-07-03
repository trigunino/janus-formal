from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_equation_of_state_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_equation_of_state_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "kinetic_theory_bibliography_checked": True,
        "Fermi_Dirac_energy_pressure_integrals_imported": True,
        "fermion_distribution_gate_declared": True,
        "Dirac_regime_selection_gate_declared": True,
        "Dirac_mass_temperature_law_gate_declared": True,
        "plus_rho_integral_declared": True,
        "plus_pressure_integral_declared": True,
        "minus_rho_integral_declared": True,
        "minus_pressure_integral_declared": True,
        "Z2Sigma_projection_required": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_distribution_of_a_ready": False,
        "minus_distribution_of_a_ready": False,
        "plus_regime_selected": False,
        "minus_regime_selected": False,
        "plus_mass_temperature_law_ready": False,
        "minus_mass_temperature_law_ready": False,
        "plus_equation_of_state_derived": False,
        "minus_equation_of_state_derived": False,
        "projected_equation_of_state_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-equation-of-state-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "relativistic kinetic theory of ideal Fermi gases",
            "Ma/Bertschinger massive-neutrino phase-space treatment",
            "cosmological massive-fermion energy-density and pressure integrals",
        ],
        "bibliography_result": (
            "The literature supplies the kinetic integrals for rho(a) and p(a). "
            "It does not supply the active Janus Z2/Sigma distributions, regimes, "
            "mass/temperature laws or projected equation of state."
        ),
        "source_links": [
            "https://arxiv.org/pdf/astro-ph/9506072",
            "https://inspirehep.net/literature/396100",
            "https://academic.oup.com/mnras/article/478/1/516/4990652",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "rho_pm": "rho_pm(a) = g/(2 pi^2) integral dp p^2 E_pm(p,a) f_pm(p,a)",
            "pressure_pm": "p_pm(a) = g/(6 pi^2) integral dp p^4/E_pm(p,a) f_pm(p,a)",
            "relativistic_limit": "w_pm = 1/3 only after m_pm/T_pm << 1 is derived",
            "massive_limit": "w_pm -> 0 only after m_pm/T_pm >> 1 and decoupling are derived",
        },
        "dirac_equation_of_state_ledger_declared": all(declared.values()),
        "dirac_equation_of_state_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_fermion_distribution_of_a_gate",
            "pass_Dirac_regime_selection_gate",
            "pass_Dirac_mass_temperature_law_gate",
            "derive_plus_minus_rho_p_integrals",
            "project_equation_of_state_to_sector_density_pressure_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Equation Of State Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_equation_of_state_ledger_declared']}`",
        f"Equation of state ready: `{payload['dirac_equation_of_state_ready']}`",
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

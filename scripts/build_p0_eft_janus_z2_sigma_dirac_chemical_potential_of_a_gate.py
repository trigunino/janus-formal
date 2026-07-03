from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_chemical_potential_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_chemical_potential_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "Fermi_Dirac_chemical_potential_bibliography_checked": True,
        "number_constraint_equation_declared": True,
        "number_normalization_gate_declared": True,
        "mass_temperature_law_gate_declared": True,
        "regime_selection_gate_declared": True,
        "plus_chemical_potential_equation_declared": True,
        "minus_chemical_potential_equation_declared": True,
        "Z2Sigma_projected_chemical_potential_declared": True,
        "no_chemical_potential_fit": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_number_normalization_ready": False,
        "minus_number_normalization_ready": False,
        "plus_mass_temperature_law_ready": False,
        "minus_mass_temperature_law_ready": False,
        "plus_regime_selected": False,
        "minus_regime_selected": False,
        "plus_chemical_potential_solved": False,
        "minus_chemical_potential_solved": False,
        "projected_chemical_potential_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-chemical-potential-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Fermi-Dirac number-density constraint for chemical potential",
            "Lesgourgues/Pastor massive-neutrino chemical/degeneracy parameter treatment",
            "cosmological chemical/kinetic equilibrium literature",
        ],
        "bibliography_result": (
            "Generic statistical mechanics fixes mu by inverting the number-density "
            "constraint at given temperature, mass and degeneracy. No source fixes "
            "active Janus Z2/Sigma mu_plus(a), mu_minus(a), or projected mu_Z2Sigma(a)."
        ),
        "source_links": [
            "https://arxiv.org/html/2508.20988v1",
            "https://ific.uv.es/~pastor/RINO/PREP429.pdf",
            "https://academic.oup.com/mnras/article/478/1/516/4990652",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "number_constraint": "n_pm(a)=g_pm/(2 pi^2) integral dq q^2 f_pm(q,a; mu_pm)",
            "chemical_potential_solution": "mu_pm(a) solves n_pm(a; mu_pm,T_pm,m_pm)=N_pm/a^3",
            "degeneracy_parameter": "xi_pm(a)=mu_pm(a)/T_pm(a)",
            "projection": "mu_Z2Sigma(a)=P_Z2Sigma(mu_+(a), mu_-(a)) only after plus/minus solutions exist",
        },
        "dirac_chemical_potential_ledger_declared": all(declared.values()),
        "dirac_chemical_potential_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_number_normalization_gate",
            "pass_Dirac_mass_temperature_law_gate",
            "pass_Dirac_regime_selection_gate",
            "solve_plus_minus_mu_from_number_constraints",
            "project_mu_through_Z2Sigma",
            "feed_result_to_Dirac_thermal_occupation_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Chemical Potential Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_chemical_potential_ledger_declared']}`",
        f"Chemical potential ready: `{payload['dirac_chemical_potential_ready']}`",
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

from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_thermal_occupation_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_thermal_occupation_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "Fermi_Dirac_bibliography_checked": True,
        "Fermi_Dirac_occupation_declared": True,
        "chemical_potential_policy_declared": True,
        "chemical_potential_gate_declared": True,
        "degeneracy_factor_declared": True,
        "degeneracy_factor_gate_declared": True,
        "number_normalization_gate_declared": True,
        "mass_temperature_law_gate_declared": True,
        "regime_selection_gate_declared": True,
        "plus_occupation_declared": True,
        "minus_occupation_declared": True,
        "Z2Sigma_projected_occupation_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_number_normalization_ready": False,
        "minus_number_normalization_ready": False,
        "plus_mass_temperature_law_ready": False,
        "minus_mass_temperature_law_ready": False,
        "plus_regime_selected": False,
        "minus_regime_selected": False,
        "plus_chemical_potential_derived": False,
        "minus_chemical_potential_derived": False,
        "plus_thermal_occupation_ready": False,
        "minus_thermal_occupation_ready": False,
        "projected_thermal_occupation_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-thermal-occupation-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Ma/Bertschinger phase-space distribution hierarchy",
            "Lesgourgues/Pastor massive-neutrino cosmology review",
            "Fermi-Dirac equilibrium distribution literature",
            "active Dirac chemical-potential gate",
            "active Dirac degeneracy-factor gate",
        ],
        "bibliography_result": (
            "Primary cosmology sources supply Fermi-Dirac occupation and phase-space "
            "moment machinery. They do not fix active Janus Z2/Sigma chemical "
            "potentials, degeneracies, regimes or projected occupations."
        ),
        "source_links": [
            "https://arxiv.org/pdf/astro-ph/9506072",
            "https://ific.uv.es/~pastor/RINO/PREP429.pdf",
            "https://academic.oup.com/mnras/article/478/1/516/4990652",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "occupation_pm": "f_pm(q,a)=1/(exp((E_pm(q,a)-mu_pm(a))/T_pm(a))+1)",
            "energy": "E_pm(q,a)=sqrt((q/a)^2 + m_pm^2)",
            "chemical_potential_policy": "mu_pm(a) is fixed by N_pm, T_pm(a), m_pm and projection data, not observations",
            "projection": "f_Z2Sigma = P_Z2Sigma(f_+, f_-)",
        },
        "dirac_thermal_occupation_ledger_declared": all(declared.values()),
        "dirac_thermal_occupation_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_number_normalization_gate",
            "pass_Dirac_mass_temperature_law_gate",
            "pass_Dirac_regime_selection_gate",
            "pass_Dirac_chemical_potential_gate",
            "pass_Dirac_degeneracy_factor_gate",
            "derive_plus_minus_chemical_potentials",
            "project_thermal_occupation_through_Z2Sigma",
            "feed_result_to_fermion_distribution_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Thermal Occupation Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_thermal_occupation_ledger_declared']}`",
        f"Thermal occupation ready: `{payload['dirac_thermal_occupation_ready']}`",
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

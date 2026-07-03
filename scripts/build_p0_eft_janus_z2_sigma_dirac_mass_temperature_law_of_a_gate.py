from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_mass_temperature_law_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_mass_temperature_law_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "fermion_thermal_bibliography_checked": True,
        "momentum_redshift_law_imported": True,
        "relativistic_temperature_scaling_declared": True,
        "massive_decoupled_Fermi_gas_guard_declared": True,
        "Dirac_regime_selection_gate_declared": True,
        "Dirac_decoupling_condition_gate_declared": True,
        "Dirac_mass_parameter_declared": True,
        "Z2Sigma_projection_required": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "relativistic_or_massive_regime_derived": False,
        "decoupling_scale_derived": False,
        "plus_mass_temperature_law_ready": False,
        "minus_mass_temperature_law_ready": False,
        "projected_mass_temperature_law_ready": False,
        "Dirac_mass_temperature_law_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-mass-temperature-law-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "standard thermal relic temperature-redshift literature",
            "decoupled massive Fermi gas cosmology literature",
            "Dirac regime-selection gate",
            "Dirac decoupling-condition gate",
            "active Dirac/spinorial fermion route-selection gate",
        ],
        "bibliography_result": (
            "Generic cosmology supplies momentum redshift and T_scaling ~ a^-1 "
            "for relativistic decoupled species. Massive decoupled Fermi gases "
            "require a regime/decoupling prescription; the active Janus Z2/Sigma "
            "model must derive that prescription rather than fit it."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "momentum_redshift": "p_comoving = a * p_physical = constant",
            "relativistic_scaling": "T_pm(a) = T_dec_pm * a_dec_pm / a when the species is relativistic and decoupled",
            "massive_guard": "massive decoupled Fermi gas may need effective T(a), mu(a), not a naive thermal law",
            "distribution_energy": "E_pm(a,p) = sqrt((p/a)^2 + m_pm^2)",
        },
        "dirac_mass_temperature_ledger_declared": all(declared.values()),
        "dirac_mass_temperature_law_of_a_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_regime_selection_gate",
            "pass_Dirac_decoupling_condition_gate",
            "derive_plus_minus_mass_temperature_laws",
            "project_mass_temperature_law_through_Z2Sigma_throat",
            "propagate_mass_temperature_law_to_fermion_distribution_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Mass/Temperature Law Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_mass_temperature_ledger_declared']}`",
        f"Mass/temperature law ready: `{payload['dirac_mass_temperature_law_of_a_ready']}`",
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

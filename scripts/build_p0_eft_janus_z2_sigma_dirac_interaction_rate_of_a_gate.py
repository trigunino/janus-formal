from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_interaction_rate_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_interaction_rate_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "interaction_rate_bibliography_checked": True,
        "Gamma_equals_number_density_times_thermal_cross_section_imported": True,
        "plus_bath_density_declared": True,
        "minus_bath_density_declared": True,
        "plus_thermal_cross_section_declared": True,
        "minus_thermal_cross_section_declared": True,
        "thermal_cross_section_gate_declared": True,
        "Z2Sigma_projection_required": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_bath_density_of_a_ready": False,
        "minus_bath_density_of_a_ready": False,
        "plus_thermal_cross_section_of_a_ready": False,
        "minus_thermal_cross_section_of_a_ready": False,
        "plus_interaction_rate_of_a_ready": False,
        "minus_interaction_rate_of_a_ready": False,
        "projected_interaction_rate_of_a_ready": False,
        "Dirac_interaction_rate_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-interaction-rate-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "thermal relic freeze-out literature",
            "photon/neutrino decoupling Gamma/H literature",
            "active Dirac number-density gate",
            "Dirac thermal cross-section gate",
        ],
        "bibliography_result": (
            "Generic kinetic decoupling uses Gamma(a)=n_bath(a)<sigma v>(a). "
            "For Janus Z2/Sigma, the bath density, thermal cross section, and "
            "projection must be derived from the active action/topology."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "plus_rate": "Gamma_+(a)=n_bath,+(a)<sigma v>_+(a)",
            "minus_rate": "Gamma_-(a)=n_bath,-(a)<sigma v>_-(a)",
            "projected_rate": "Gamma_Z2Sigma(a)=P_Z2Sigma(Gamma_+(a), Gamma_-(a))",
        },
        "dirac_interaction_rate_ledger_declared": all(declared.values()),
        "dirac_interaction_rate_of_a_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_plus_minus_bath_densities_of_a",
            "derive_plus_minus_thermal_cross_sections_of_a",
            "pass_Dirac_thermal_cross_section_of_a_gate",
            "project_interaction_rate_through_Z2Sigma_throat",
            "feed_Gamma_plus_minus_to_Dirac_decoupling_condition_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Interaction Rate Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_interaction_rate_ledger_declared']}`",
        f"Interaction rate ready: `{payload['dirac_interaction_rate_of_a_ready']}`",
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

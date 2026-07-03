from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_thermal_cross_section_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_thermal_cross_section_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "cross_section_bibliography_checked": True,
        "thermal_average_sigma_v_imported": True,
        "Gondolo_Gelmini_relativistic_average_imported": True,
        "plus_matrix_element_declared": True,
        "minus_matrix_element_declared": True,
        "Dirac_Holst_vertex_gate_declared": True,
        "plus_phase_space_measure_declared": True,
        "minus_phase_space_measure_declared": True,
        "mass_temperature_law_required": True,
        "Z2Sigma_projection_required": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_matrix_element_ready": False,
        "minus_matrix_element_ready": False,
        "plus_phase_space_measure_ready": False,
        "minus_phase_space_measure_ready": False,
        "plus_thermal_cross_section_of_a_ready": False,
        "minus_thermal_cross_section_of_a_ready": False,
        "projected_thermal_cross_section_of_a_ready": False,
        "Dirac_thermal_cross_section_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-thermal-cross-section-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Gondolo and Gelmini 1991 thermal average",
            "thermal relic Boltzmann literature",
            "active Dirac mass/temperature gate",
            "active Dirac-Holst vertex gate",
        ],
        "bibliography_result": (
            "The literature supplies the generic thermal average <sigma v> and "
            "the Gondolo-Gelmini relativistic averaging method. It does not "
            "supply the Janus Z2/Sigma matrix element, phase-space measure, or "
            "projection."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "thermal_average": "<sigma v>_pm(a)=thermal_average_pm[sigma_pm(s) v_rel; f_pm(a,p)]",
            "matrix_element_dependency": "sigma_pm(s) derived from |M_pm^Z2Sigma|^2",
            "projected_cross_section": "<sigma v>_Z2Sigma(a)=P_Z2Sigma(<sigma v>_+(a),<sigma v>_-(a))",
        },
        "dirac_thermal_cross_section_ledger_declared": all(declared.values()),
        "dirac_thermal_cross_section_of_a_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_plus_minus_Z2Sigma_matrix_elements",
            "pass_Dirac_Holst_vertex_of_a_gate",
            "derive_plus_minus_phase_space_measures",
            "pass_Dirac_mass_temperature_law_of_a_gate",
            "project_thermal_cross_section_through_Z2Sigma_throat",
            "feed_cross_sections_to_Dirac_interaction_rate_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Thermal Cross Section Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_thermal_cross_section_ledger_declared']}`",
        f"Thermal cross section ready: `{payload['dirac_thermal_cross_section_of_a_ready']}`",
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

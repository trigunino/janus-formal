from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_mass_term_from_action_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_mass_term_from_action_gate.json")


def build_payload() -> dict:
    declared = {
        "Dirac_mass_term_bibliography_checked": True,
        "projected_Dirac_action_gate_declared": True,
        "scalar_mass_law_gate_declared": True,
        "mass_bilinear_declared": True,
        "plus_mass_coefficient_declared": True,
        "minus_mass_coefficient_declared": True,
        "Z2Sigma_projected_mass_coefficient_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "projected_Dirac_action_ready": False,
        "plus_Dirac_action_reduced": False,
        "minus_Dirac_action_reduced": False,
        "plus_mass_bilinear_identified": False,
        "minus_mass_bilinear_identified": False,
        "plus_mass_coefficient_from_action_derived": False,
        "minus_mass_coefficient_from_action_derived": False,
        "projected_mass_coefficient_derived": False,
        "mass_term_from_action_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-mass-term-from-action-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "curved-spacetime Dirac action in tetrad form",
            "Einstein-Cartan/Holst fermion action literature",
            "active projected Dirac action reduction gate",
            "active plus/minus Dirac action local reduction gate",
        ],
        "source_links": [
            "https://arxiv.org/html/2503.03918v1",
            "https://arxiv.org/pdf/0812.1298",
            "https://arxiv.org/pdf/1803.10621",
        ],
        "bibliography_result": (
            "Generic curved-space Dirac theory supplies the mass bilinear m psibar psi. "
            "The active Janus Z2/Sigma model still has to identify and project the "
            "plus/minus mass coefficients from its reduced Dirac actions."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "mass_bilinear": "L_m^(pm)=e_pm m_pm(a) psibar_pm psi_pm",
            "plus_extraction": "m_+(a)=coefficient_of(psibar_+ psi_+) in S_D,+",
            "minus_extraction": "m_-(a)=coefficient_of(psibar_- psi_-) in S_D,-",
            "projection": "m_Z2Sigma(a)=P_Z2Sigma(m_+(a),m_-(a))",
        },
        "dirac_mass_term_from_action_ledger_declared": all(declared.values()),
        "dirac_mass_term_from_action_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_projected_Dirac_action_reduction_gate",
            "pass_plus_minus_Dirac_action_local_reduction_gate",
            "identify_plus_minus_mass_bilinears",
            "extract_plus_minus_mass_coefficients_from_action",
            "project_mass_coefficient_through_Z2Sigma",
            "feed_result_to_Dirac_scalar_mass_law_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Mass Term From Action Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_mass_term_from_action_ledger_declared']}`",
        f"Mass term extraction ready: `{payload['dirac_mass_term_from_action_ready']}`",
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

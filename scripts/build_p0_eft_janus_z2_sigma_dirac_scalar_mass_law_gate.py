from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_scalar_mass_law_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_scalar_mass_law_gate.json")


def build_payload() -> dict:
    declared = {
        "Dirac_mass_scalar_bibliography_checked": True,
        "projected_Dirac_action_gate_declared": True,
        "mass_temperature_law_gate_declared": True,
        "plus_mass_term_declared": True,
        "minus_mass_term_declared": True,
        "scalar_under_local_Lorentz_criterion_declared": True,
        "Z2Sigma_projection_mass_criterion_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_projected_Dirac_action_ready": False,
        "minus_projected_Dirac_action_ready": False,
        "plus_mass_term_from_action_derived": False,
        "minus_mass_term_from_action_derived": False,
        "plus_scalar_mass_derived": False,
        "minus_scalar_mass_derived": False,
        "projected_scalar_mass_derived": False,
        "scalar_mass_law_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-scalar-mass-law-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "standard curved-spacetime Dirac/tetrad action literature",
            "Einstein-Cartan-Dirac/Holst fermion literature",
            "active projected Dirac action reduction gate",
            "active Dirac mass term from action gate",
        ],
        "source_links": [
            "https://arxiv.org/html/2503.03918v1",
            "https://link.aps.org/doi/10.1103/PhysRevD.79.064029",
            "https://arxiv.org/pdf/1803.10621",
        ],
        "bibliography_result": (
            "The literature supplies the generic Dirac mass term as a local Lorentz scalar. "
            "The active Janus Z2/Sigma model must still derive plus/minus mass terms from "
            "the projected Dirac action and show that the projection keeps a scalar mass law."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "mass_term_pm": "S_m^(pm)=int e_pm m_pm(a) psibar_pm psi_pm",
            "scalar_criterion": "m_pm(a) is scalar under local Lorentz/tetrad rotations",
            "projection": "m_Z2Sigma(a)=P_Z2Sigma(m_+(a),m_-(a))",
            "fit_guard": "m_pm(a) must be action/projection-derived, not observation-fitted",
        },
        "dirac_scalar_mass_law_ledger_declared": all(declared.values()),
        "dirac_scalar_mass_law_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "projected_Dirac_action_mass_term"
        ),
        "next_required": [
            "pass_projected_Dirac_action_reduction_gate",
            "pass_Dirac_mass_term_from_action_gate",
            "derive_plus_minus_mass_terms_from_action",
            "prove_plus_minus_mass_terms_are_scalars",
            "project_scalar_mass_law_through_Z2Sigma",
            "feed_result_to_Dirac_mass_temperature_law_gate",
            "feed_result_to_Dirac_radial_energy_dispersion_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Scalar Mass Law Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_scalar_mass_law_ledger_declared']}`",
        f"Scalar mass law ready: `{payload['dirac_scalar_mass_law_ready']}`",
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

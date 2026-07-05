from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_distribution_isotropy_anisotropic_stress_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_distribution_isotropy_anisotropic_stress_gate.json")


def build_payload() -> dict:
    declared = {
        "isotropic_distribution_bibliography_checked": True,
        "fermion_distribution_gate_declared": True,
        "plus_momentum_isotropy_criterion_declared": True,
        "minus_momentum_isotropy_criterion_declared": True,
        "projected_isotropy_criterion_declared": True,
        "anisotropic_stress_tensor_declared": True,
        "no_anisotropic_stress_assumption": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_distribution_ready": False,
        "minus_distribution_ready": False,
        "plus_momentum_isotropy_derived": False,
        "minus_momentum_isotropy_derived": False,
        "projected_momentum_isotropy_derived": False,
        "plus_anisotropic_stress_zero_derived": False,
        "minus_anisotropic_stress_zero_derived": False,
        "projected_anisotropic_stress_zero_derived": False,
        "FLRW_isotropy_closure_ready": False,
    }
    return {
        "status": "janus-z2-sigma-distribution-isotropy-anisotropic-stress-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Ma/Bertschinger Boltzmann hierarchy and anisotropic stress moments",
            "Einstein-Vlasov/relativistic kinetic stress-energy moment literature",
            "standard cosmological perfect-fluid reduction from isotropic distributions",
            "Janus Z2/Sigma Dirac Fermi-Dirac isotropy gate",
            "Janus Z2/Sigma radial occupation projection gate",
        ],
        "source_links": [
            "https://arxiv.org/pdf/astro-ph/9506072",
            "https://pmc.ncbi.nlm.nih.gov/articles/PMC5255633/",
            "https://ned.ipac.caltech.edu/level5/March02/Bertschinger/Bert4_3.html",
        ],
        "bibliography_result": (
            "The literature supplies the standard kinetic moment and anisotropic-stress "
            "definitions. The active Janus Z2/Sigma model still has to derive isotropy "
            "for the projected plus/minus distributions before using a perfect-fluid FLRW closure."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "sector_isotropy": "f_pm(q_vec,a)=f_pm(|q|,a)",
            "anisotropic_stress": "pi_ij^(pm)=T_ij^(pm)-p_pm h_ij^(pm)",
            "projected_anisotropic_stress": "pi_ij^Z2Sigma=P_Z2Sigma(pi_ij^+,pi_ij^-)",
            "FLRW_condition": "pi_ij^(pm)=0 and pi_ij^Z2Sigma=0",
        },
        "distribution_isotropy_ledger_declared": all(declared.values()),
        "distribution_isotropy_closure_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "active_distribution_isotropy"
        ),
        "next_required": [
            "pass_fermion_distribution_of_a_gate",
            "derive_plus_minus_momentum_isotropy",
            "pass_Dirac_Fermi_Dirac_isotropy_gate",
            "pass_radial_occupation_projection_gate",
            "derive_projected_momentum_isotropy",
            "prove_projected_anisotropic_stress_zero",
            "feed_result_to_kinetic_moment_fluid_closure_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Distribution Isotropy and Anisotropic Stress Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['distribution_isotropy_ledger_declared']}`",
        f"Closure ready: `{payload['distribution_isotropy_closure_ready']}`",
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

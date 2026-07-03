from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_fermi_dirac_isotropy_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_fermi_dirac_isotropy_gate.json")


def build_payload() -> dict:
    declared = {
        "Fermi_Dirac_isotropy_bibliography_checked": True,
        "thermal_occupation_gate_declared": True,
        "distribution_isotropy_gate_declared": True,
        "radial_energy_criterion_declared": True,
        "plus_radial_occupation_criterion_declared": True,
        "minus_radial_occupation_criterion_declared": True,
        "projection_preserves_isotropy_criterion_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_thermal_occupation_ready": False,
        "minus_thermal_occupation_ready": False,
        "plus_energy_radial_derived": False,
        "minus_energy_radial_derived": False,
        "projected_occupation_radial_derived": False,
        "plus_momentum_isotropy_derived": False,
        "minus_momentum_isotropy_derived": False,
        "projected_momentum_isotropy_derived": False,
        "Fermi_Dirac_isotropy_closure_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-fermi-dirac-isotropy-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Ma/Bertschinger cosmological phase-space hierarchy",
            "Lesgourgues/Pastor massive-neutrino Fermi-Dirac distribution review",
            "standard equilibrium Fermi-Dirac distribution literature",
            "Janus Z2/Sigma Dirac radial energy dispersion gate",
            "Janus Z2/Sigma radial occupation projection gate",
        ],
        "source_links": [
            "https://arxiv.org/pdf/astro-ph/9506072",
            "https://ific.uv.es/~pastor/RINO/PREP429.pdf",
            "https://arxiv.org/abs/astro-ph/9308006",
        ],
        "bibliography_result": (
            "The standard result is usable conditionally: a Fermi-Dirac occupation "
            "with E=E(|q|,a), mu=mu(a), T=T(a) is isotropic in momentum. "
            "The active Janus Z2/Sigma proof must still derive radial plus/minus energies "
            "and show that the projection preserves isotropy."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "occupation_pm": "f_pm(q_vec,a)=1/(exp((E_pm(|q|,a)-mu_pm(a))/T_pm(a))+1)",
            "radial_energy_condition": "E_pm(q_vec,a)=E_pm(|q|,a)",
            "isotropy_implication": "occupation_pm depends on q_vec only through |q|",
            "projection_condition": "P_Z2Sigma preserves radial dependence of f_+ and f_-",
        },
        "dirac_fermi_dirac_isotropy_ledger_declared": all(declared.values()),
        "dirac_fermi_dirac_isotropy_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_thermal_occupation_of_a_gate",
            "pass_Dirac_radial_energy_dispersion_gate",
            "derive_plus_minus_radial_energy_dispersion",
            "pass_radial_occupation_projection_gate",
            "prove_Z2Sigma_projection_preserves_radial_occupation",
            "feed_result_to_distribution_isotropy_anisotropic_stress_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Fermi-Dirac Isotropy Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_fermi_dirac_isotropy_ledger_declared']}`",
        f"Isotropy ready: `{payload['dirac_fermi_dirac_isotropy_ready']}`",
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

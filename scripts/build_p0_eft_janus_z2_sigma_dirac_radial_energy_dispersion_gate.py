from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_radial_energy_dispersion_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_radial_energy_dispersion_gate.json")


def build_payload() -> dict:
    declared = {
        "radial_energy_bibliography_checked": True,
        "mass_temperature_law_gate_declared": True,
        "Fermi_Dirac_isotropy_gate_declared": True,
        "comoving_momentum_redshift_declared": True,
        "plus_energy_formula_declared": True,
        "minus_energy_formula_declared": True,
        "scalar_mass_law_criterion_declared": True,
        "FLRW_momentum_frame_criterion_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_mass_law_ready": False,
        "minus_mass_law_ready": False,
        "plus_scalar_mass_derived": False,
        "minus_scalar_mass_derived": False,
        "plus_FLRW_momentum_frame_derived": False,
        "minus_FLRW_momentum_frame_derived": False,
        "plus_radial_energy_derived": False,
        "minus_radial_energy_derived": False,
        "projected_radial_energy_derived": False,
        "radial_energy_dispersion_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-radial-energy-dispersion-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Ma/Bertschinger massive-particle phase-space convention",
            "Lesgourgues/Pastor massive-neutrino comoving momentum energy",
            "active Dirac mass/temperature law gate",
            "active FLRW momentum frame gate",
            "active Dirac scalar mass law gate",
        ],
        "source_links": [
            "https://arxiv.org/abs/astro-ph/9506072",
            "https://ific.uv.es/~pastor/RINO/PREP429.pdf",
        ],
        "bibliography_result": (
            "Standard cosmological kinetic theory supplies epsilon=(q^2+a^2m^2)^(1/2). "
            "This proves radiality only after the active Janus plus/minus FLRW momentum "
            "frames and scalar mass laws are derived."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "comoving_momentum": "q=a p_physical",
            "epsilon_pm": "epsilon_pm(q,a)=sqrt(q^2 + a^2 m_pm(a)^2)",
            "physical_energy_pm": "E_pm(q,a)=epsilon_pm(q,a)/a",
            "radiality": "E_pm(q_vec,a)=E_pm(|q|,a) if m_pm(a) is scalar in an FLRW momentum frame",
        },
        "dirac_radial_energy_dispersion_ledger_declared": all(declared.values()),
        "dirac_radial_energy_dispersion_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_mass_temperature_law_of_a_gate",
            "pass_Dirac_scalar_mass_law_gate",
            "derive_plus_minus_scalar_mass_laws",
            "pass_FLRW_momentum_frame_gate",
            "derive_plus_minus_FLRW_momentum_frames",
            "prove_projected_radial_energy_dispersion",
            "feed_result_to_Dirac_Fermi_Dirac_isotropy_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Radial Energy Dispersion Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_radial_energy_dispersion_ledger_declared']}`",
        f"Radial dispersion ready: `{payload['dirac_radial_energy_dispersion_ready']}`",
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

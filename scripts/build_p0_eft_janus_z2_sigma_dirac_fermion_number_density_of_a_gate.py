from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_fermion_number_density_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_fermion_number_density_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "Dirac_number_density_bibliography_checked": True,
        "Dirac_U1_current_imported": True,
        "covariant_current_conservation_declared": True,
        "FLRW_dilution_law_derived": True,
        "Dirac_number_normalization_gate_declared": True,
        "anomaly_or_source_guard_declared": True,
        "Z2Sigma_projection_required": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_number_normalization_derived": False,
        "minus_number_normalization_derived": False,
        "projected_number_density_ready": False,
        "Dirac_fermion_number_density_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-fermion-number-density-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Dirac U(1) Noether current literature",
            "standard FLRW particle-number conservation",
            "Dirac number-normalization gate",
            "active Dirac/spinorial fermion route-selection gate",
        ],
        "bibliography_result": (
            "Generic Dirac theory supplies J^mu = psi_bar gamma^mu psi and "
            "covariant conservation when no anomaly/source is active. FLRW then "
            "gives n_pm(a) = N_pm/a^3. The Janus Z2/Sigma action must still "
            "derive N_plus, N_minus, and the projected throat density."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "dirac_current": "J_pm^mu = psi_bar_pm gamma^mu psi_pm",
            "covariant_conservation": "nabla_mu J_pm^mu = 0 unless an active anomaly/source is derived",
            "flrw_dilution": "n_pm(a) = N_pm / a^3",
            "projection": "n_Z2Sigma(a) = project_Z2Sigma(N_+, N_-) / a^3",
        },
        "dirac_number_density_ledger_declared": all(declared.values()),
        "dirac_fermion_number_density_of_a_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_Dirac_number_normalization_gate",
            "propagate_number_density_to_fermion_distribution_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Fermion Number Density Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_number_density_ledger_declared']}`",
        f"Number density ready: `{payload['dirac_fermion_number_density_of_a_ready']}`",
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

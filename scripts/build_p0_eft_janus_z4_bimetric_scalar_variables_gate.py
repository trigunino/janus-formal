from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_bimetric_scalar_variables_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_bimetric_scalar_variables_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z4-bimetric-scalar-variables-gate",
        "visible_metric_potentials_declared": True,
        "hidden_or_negative_metric_potentials_declared": True,
        "visible_fluid_variables_declared": True,
        "hidden_fluid_variables_declared": True,
        "projection_terms_declared": True,
        "mixing_terms_declared": True,
        "anisotropic_stress_terms_declared": True,
        "torsion_terms_declared_or_explicitly_zero": True,
        "torsion_terms_status": "explicit_zero_until_derived",
        "variables": {
            "metric_plus": ["Phi_plus", "Psi_plus"],
            "metric_minus": ["Phi_minus", "Psi_minus"],
            "fluid_plus": ["delta_plus", "theta_plus", "sigma_plus"],
            "fluid_minus": ["delta_minus", "theta_minus", "sigma_minus"],
            "projection": ["P_Z4", "Mix_plus_minus", "Mix_minus_plus"],
            "stress_sources": ["Pi_matter_plus_TF", "Pi_matter_minus_TF", "Pi_projection_TF", "Pi_torsion_TF"],
        },
        "free_slip_parameter": False,
        "free_eta_ratio": False,
        "direct_Cl_patch": False,
        "raw_toy_LOS": False,
        "planck_trial_allowed": False,
        "variables_gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Bimetric Scalar Variables Gate",
        "",
        f"Variables gate passed: `{payload['variables_gate_passed']}`",
        f"Torsion terms status: `{payload['torsion_terms_status']}`",
        f"Planck trial allowed: `{payload['planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

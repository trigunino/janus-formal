from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_prediction_vector_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_prediction_vector_gate.json")


def build_payload() -> dict:
    closure = {
        "growth_perturbation_equations_derived": True,
        "numerical_background_closure_ready": False,
        "numerical_H_Z2Sigma_ready": False,
        "numerical_Omega_m_Z2Sigma_ready": False,
        "numerical_mu_Z2Sigma_ready": False,
        "numerical_slip_Z2Sigma_ready": False,
        "numerical_friction_Z2Sigma_ready": False,
        "initial_condition_policy_declared": True,
        "sigma8_normalization_policy_declared": True,
        "archived_holst_growth_solver_reuse_forbidden": True,
        "archived_z4_growth_solver_reuse_forbidden": True,
    }
    return {
        "status": "janus-z2-sigma-growth-prediction-vector-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "closure": closure,
        "growth_prediction_vector_prerequisites_ready": all(closure.values()),
        "z2_sigma_growth_prediction_vector_ready": False,
        "vector_columns_required": ["dataset", "z", "f_sigma8_z2_sigma", "source_equation_hash"],
        "initial_condition_policy": "declare before integration; no fitted high-z slope injection",
        "sigma8_normalization_policy": "declare whether sigma8_0 is theory-derived or diagnostic-normalized",
        "forbidden_reuse": [
            "scripts.run_p0_eft_holst_immirzi_growth_solver.integrate_growth_holst",
            "scripts.run_p0_eft_holst_membrane_co_optimisation.branch_curve",
            "archived_z4_mu_sigma_tables",
        ],
        "next_required": [
            "close_z2_sigma_numerical_background_closure_gate",
            "derive_numeric_mu_slip_friction_Z2Sigma_from_perturbation_closure",
            "implement_growth_ode_integrator_for_active_z2_sigma_core",
            "export_fsigma8_prediction_vector_at_sdss_eboss_redshifts",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Growth Prediction Vector Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Bibliography checked: `{payload['bibliography_checked']}`",
        f"Prerequisites ready: `{payload['growth_prediction_vector_prerequisites_ready']}`",
        f"Prediction vector ready: `{payload['z2_sigma_growth_prediction_vector_ready']}`",
        "",
        "## Missing Numeric Closures",
    ]
    lines.extend(
        f"- `{key}`"
        for key, value in payload["closure"].items()
        if not value
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

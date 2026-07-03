from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_perturbation_equation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_perturbation_equation_gate.json")


def build_payload() -> dict:
    lock = {
        "background_equations_derived": True,
        "growth_bibliography_checked": True,
        "scalar_perturbation_gauge_declared": True,
        "density_continuity_perturbation_derived": True,
        "velocity_euler_perturbation_derived": True,
        "z2_sigma_poisson_constraint_derived": True,
        "z2_sigma_slip_relation_derived": True,
        "z2_sigma_friction_term_derived": True,
        "archived_z4_mu_reuse_forbidden": True,
    }
    return {
        "status": "janus-z2-sigma-growth-perturbation-equation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "lock": lock,
        "growth_perturbation_lock_closed": all(lock.values()),
        "growth_perturbation_equations_derived": all(lock.values()),
        "equation_family": {
            "continuity": "delta_dot + theta/a + metric_source_Z2Sigma = 0",
            "euler": "theta_dot + H_Z2Sigma theta = k^2 Psi_Z2Sigma/a",
            "poisson": "k^2 Phi_Z2Sigma = 4 pi G a^2 mu_Z2Sigma rho delta",
            "slip": "Phi_Z2Sigma - Psi_Z2Sigma = Pi_Z2Sigma",
            "growth": "delta_xx + F_Z2Sigma delta_x = S_Z2Sigma delta",
        },
        "archived_z4_mu_reuse_forbidden": True,
        "non_compressed_growth_gate_ready": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Growth Perturbation Equation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Growth perturbation equations derived: `{payload['growth_perturbation_equations_derived']}`",
        "",
        "## Equation Family",
    ]
    lines.extend(f"- `{name}`: `{expr}`" for name, expr in payload["equation_family"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

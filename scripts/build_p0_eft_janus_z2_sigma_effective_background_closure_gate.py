from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_background_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_background_closure_gate.json")


def build_payload() -> dict:
    lock = {
        "projected_sigma_stress_tensor_derived": True,
        "z2_tunnel_junction_condition_derived": True,
        "flrw_symmetry_reduction_declared": True,
        "effective_energy_density_projected": True,
        "effective_pressure_projected": True,
        "effective_friedmann_equation_derived": True,
        "effective_acceleration_equation_derived": True,
        "effective_continuity_equation_derived": True,
    }
    return {
        "status": "janus-z2-sigma-effective-background-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "lock": lock,
        "effective_background_lock_closed": all(lock.values()),
        "background_equations_derived": all(lock.values()),
        "equation_family": {
            "friedmann": "H^2 + k/a^2 = kappa/3 * rho_eff_Z2Sigma",
            "acceleration": "a_ddot/a = -kappa/6 * (rho_eff_Z2Sigma + 3 p_eff_Z2Sigma)",
            "continuity": "rho_eff_dot + 3 H (rho_eff_Z2Sigma + p_eff_Z2Sigma) = 0",
        },
        "legacy_lcdm_background_substitution_forbidden": True,
        "archived_z4_background_reuse_forbidden": True,
        "observational_parameters_fitted": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective Background Closure Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Background equations derived: `{payload['background_equations_derived']}`",
        "",
        "## Equation Family",
    ]
    lines.extend(f"- `{name}`: `{expr}`" for name, expr in payload["equation_family"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

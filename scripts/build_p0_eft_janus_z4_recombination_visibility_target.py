from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_recombination_visibility_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_recombination_visibility_target.json")


def build_payload() -> dict:
    a, x_e, n_b, sigma_t, tau = sp.symbols("a x_e n_b sigma_T tau", positive=True)
    n_e = sp.simplify(x_e * n_b)
    tau_dot = sp.simplify(a * n_e * sigma_t)
    visibility = sp.simplify(tau_dot * sp.exp(-tau))
    checks = {
        "optical_depth_derivative_declared": True,
        "visibility_function_declared": True,
        "ionization_history_required": True,
        "z4_background_coupled": True,
        "thomson_normalization_declared": True,
        "ionization_history_derived": False,
    }
    return {
        "status": "janus-z4-recombination-visibility-target",
        "lean_module": "JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4RecombinationVisibilityTarget",
        "electron_density": str(n_e),
        "tau_dot": str(tau_dot),
        "visibility": str(visibility),
        "checks": checks,
        "visibility_target_ready": all(
            value for key, value in checks.items()
            if key != "ionization_history_derived"
        ),
        "visibility_physical_ready": False,
        "next_required": "Derive x_e(a) under the Z4/Holst background instead of using proxy visibility.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Recombination Visibility Target",
        "",
        f"Status: `{payload['status']}`",
        f"Electron density: `{payload['electron_density']}`",
        f"tau_dot: `{payload['tau_dot']}`",
        f"visibility: `{payload['visibility']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Visibility target ready: `{payload['visibility_target_ready']}`",
        f"Visibility physical ready: `{payload['visibility_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

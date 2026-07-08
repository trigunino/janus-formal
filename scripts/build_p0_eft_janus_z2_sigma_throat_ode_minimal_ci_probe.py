from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_throat_ode import solve_minimal_ci_throat_family


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_ode_minimal_ci_probe.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_ode_minimal_ci_probe.json")


def build_payload() -> dict:
    solution = solve_minimal_ci_throat_family(
        rho_grid=[0.0, 0.25, 0.5, 1.0, 1.5],
        R0_values=[0.5, 1.0, 2.0],
    )
    return {
        "status": "janus-z2-sigma-throat-ode-minimal-ci-probe",
        "active_core": solution["active_core"],
        "source": "active_local_throat_ode_analysis",
        "normalized_ode": solution["normalized_ode"],
        "minimal_normalized_initial_conditions": solution["minimal_normalized_initial_conditions"],
        "normalized_solution_closed_form": solution["normalized_solution_closed_form"],
        "normalized_solution_unique_under_minimal_CI": solution[
            "normalized_solution_unique_under_minimal_CI"
        ],
        "normalized_ode_residual_max_abs": solution["normalized_ode_residual_max_abs"],
        "throat_is_minimal": solution["throat_is_minimal"],
        "R0_unique": solution["R0_unique"],
        "R0_scale_degenerate": solution["R0_scale_degenerate"],
        "R0_values_sampled": solution["R0_values"],
        "distinct_physical_profiles_sampled": solution["distinct_physical_profiles_sampled"],
        "normalized_reconstruction_error_max_abs": solution[
            "normalized_reconstruction_error_max_abs"
        ],
        "interpretation": (
            "The local throat ODE is solved uniquely only after normalizing by R0. "
            "It does not fix an absolute throat scale. R0 remains a homothetic modulus "
            "unless an additional global or boundary selection law is supplied."
        ),
        "next_required": [
            "supply_global_regular_tunnel_selector_if_R0_must_be_fixed",
            "or_treat_R0_as_scale_modulus_in_local_regular_sigma_branch",
        ],
        "probe_passed": solution["normalized_solution_unique_under_minimal_CI"]
        and solution["R0_scale_degenerate"]
        and not solution["R0_unique"],
    }


def render_markdown(payload: dict) -> str:
    ic = payload["minimal_normalized_initial_conditions"]
    r0_ic = ic["r(0)"]
    rp0_ic = ic["r'(0)"]
    lines = [
        "# Janus Z2/Sigma Throat ODE Minimal C.I. Probe",
        "",
        f"Normalized ODE: `{payload['normalized_ode']}`",
        f"Minimal C.I.: `r(0)={r0_ic}`, `r'(0)={rp0_ic}`",
        f"Normalized solution unique: `{payload['normalized_solution_unique_under_minimal_CI']}`",
        f"R0 unique: `{payload['R0_unique']}`",
        f"R0 scale-degenerate: `{payload['R0_scale_degenerate']}`",
        "",
        payload["interpretation"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

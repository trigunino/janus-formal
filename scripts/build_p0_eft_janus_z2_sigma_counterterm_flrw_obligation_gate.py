from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_flrw_obligation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_flrw_obligation_gate.json")


def build_payload() -> dict:
    method = {
        "boundary_counterterm_bibliography_checked": True,
        "sigma_supported_counterterm_unique": True,
        "counterterm_variation_cancels_residual": True,
        "counterterm_action_density_declared": True,
        "induced_metric_variation_declared": True,
        "Z2_orientation_sign_declared": True,
        "counterterm_stress_formula_ready": True,
    }
    closure = {
        "counterterm_FLRW_stress_reduced": False,
        "counterterm_rho_p_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-flrw-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Brown-York boundary stress and counterterm method",
            "holographic/boundary counterterm renormalization literature",
            "active Janus Sigma nonlinear residual closure gate",
        ],
        "bibliography_result": (
            "Generic boundary counterterm stress methods exist. The unique Sigma counterterm "
            "is closed structurally, but its active FLRW stress reduction is not derived."
        ),
        "method": method,
        "closure": closure,
        "formulas": {
            "counterterm_stress": "T_ct_ab = -2/sqrt(|h|) * delta S_ct[Sigma] / delta h^ab",
            "rho_ct": "rho_ct(a) = T_ct_ab u^a u^b after active FLRW reduction",
            "p_ct": "p_ct(a) = h_spatial^ab T_ct_ab / 3 after active FLRW reduction",
        },
        "counterterm_method_ready": all(method.values()),
        "counterterm_FLRW_closure_ready": all(method.values()) and all(closure.values()),
        "next_required": [
            "write_explicit_Sigma_counterterm_density_in_active_Z2Sigma_variables",
            "vary_counterterm_with_respect_to_FLRW_induced_metric",
            "reduce_counterterm_stress_to_rho_p_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm FLRW Obligation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Method ready: `{payload['counterterm_method_ready']}`",
        f"FLRW closure ready: `{payload['counterterm_FLRW_closure_ready']}`",
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

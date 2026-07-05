from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_decoupling_condition_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_decoupling_condition_gate.json")


def build_payload() -> dict:
    declared = {
        "decoupling_bibliography_checked": True,
        "Gamma_equals_H_criterion_imported": True,
        "plus_interaction_rate_declared": True,
        "minus_interaction_rate_declared": True,
        "interaction_rate_gate_declared": True,
        "Z2Sigma_Hubble_rate_required": True,
        "numerical_background_closure_gate_declared": True,
        "boundary_condition_route_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_interaction_rate_of_a_ready": False,
        "minus_interaction_rate_of_a_ready": False,
        "H_Z2Sigma_of_a_ready": False,
        "plus_decoupling_scale_ready": False,
        "minus_decoupling_scale_ready": False,
        "projected_decoupling_scale_ready": False,
        "Dirac_decoupling_condition_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-decoupling-condition-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "thermal relic freeze-out literature",
            "neutrino decoupling Gamma/H literature",
            "active Z2/Sigma background equation ledger",
            "Dirac interaction-rate gate",
            "Z2/Sigma numerical background closure gate",
        ],
        "bibliography_result": (
            "Generic decoupling uses Gamma(a_dec) = H(a_dec), or an explicitly "
            "derived boundary condition. For Janus Z2/Sigma, both Gamma_pm(a) "
            "and H_Z2Sigma(a) remain active local derivations."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "plus_decoupling": "Gamma_+(a_dec,+) = H_Z2Sigma(a_dec,+)",
            "minus_decoupling": "Gamma_-(a_dec,-) = H_Z2Sigma(a_dec,-)",
            "boundary_route": "a_dec may be fixed by Sigma boundary data only if derived from the active action",
            "temperature_link": "T_dec,pm = T_pm(a_dec,pm)",
        },
        "dirac_decoupling_ledger_declared": all(declared.values()),
        "dirac_decoupling_condition_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "active_interaction_rate_and_H_Z2Sigma_decoupling"
        ),
        "next_required": [
            "derive_plus_minus_interaction_rates_of_a",
            "pass_Dirac_interaction_rate_of_a_gate",
            "pass_Z2Sigma_numerical_background_closure_gate",
            "derive_active_H_Z2Sigma_of_a",
            "solve_Gamma_equals_H_for_a_dec_plus_minus",
            "derive_or_reject_Sigma_boundary_decoupling_condition",
            "propagate_decoupling_scales_to_regime_and_temperature_gates",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Decoupling Condition Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_decoupling_ledger_declared']}`",
        f"Decoupling ready: `{payload['dirac_decoupling_condition_ready']}`",
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

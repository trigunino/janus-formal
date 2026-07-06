from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_m30_z2_symmetric_force_cancellation.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_m30_z2_symmetric_force_cancellation.json"
)


def build_payload() -> dict:
    assumptions = {
        "free_Z2_exchange_of_two_bulk_sheets": True,
        "normal_orientation_reverses_under_Z2": True,
        "interaction_density_descends_to_quotient": True,
        "no_explicit_sigma_defect_density": True,
        "no_leaf_lapse_asymmetry_at_sigma": True,
    }
    formulae = {
        "force_before_Z2": "F_Sigma = sqrt|h| (N_+ Sbar_+|Sigma - N_- S_-|Sigma)",
        "Z2_descent_condition": "tau_Z2^*(N_+ Sbar_+) = N_- S_-",
        "orientation_condition": "tau_Z2^*(i_n mu_+) = - i_n mu_-",
        "force_after_Z2": "F_Sigma = 0",
        "nonzero_force_requires": (
            "localized Sigma defect density OR lapse/asymmetric interaction-density mismatch"
        ),
    }
    consequences = {
        "bulk_M30_interaction_generates_sigma_counterterm_under_strict_Z2": False,
        "matter_flux_transparency_supported_conditionally": True,
        "E_counterterm_from_bulk_M30_under_strict_Z2": "0",
        "R_Sigma_closed_by_M30_bulk_interaction": False,
        "need_independent_tunnel_defect_action_for_nonzero_E_counterterm": True,
    }
    return {
        "status": "janus-z2-sigma-m30-z2-symmetric-force-cancellation",
        "active_core": "Z2_tunnel_Sigma",
        "assumptions": assumptions,
        "formulae": formulae,
        "consequences": consequences,
        "gate_passed": True,
        "next_required": [
            "decide whether active tunnel is strict Z2-transparent or carries localized defect action",
            "if transparent: set M30 bulk-induced E_counterterm contribution to zero only for this channel",
            "if defect: derive independent Sigma defect density from tunnel surgery, not from M30 bulk alone",
        ],
        "verdict": (
            "Under strict Z2 descent with no localized throat defect, the M30 bulk "
            "interaction force on Sigma cancels. Therefore M30 bulk interactions do "
            "not by themselves produce a nonzero Sigma counterterm; a nonzero "
            "counterterm requires an additional tunnel-defect action or explicit "
            "Z2-asymmetric boundary data."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma M30 Z2-Symmetric Force Cancellation",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        payload["verdict"],
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Consequences"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["consequences"].items())
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

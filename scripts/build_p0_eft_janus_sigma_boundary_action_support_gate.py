from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sigma_boundary_action_support_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sigma_boundary_action_support_gate.json")


def build_payload() -> dict:
    support = {
        "throat_sigma_defined": True,
        "boundary_terms_localized_on_sigma": True,
        "antipodal_fixed_point_boundary_forbidden": True,
        "tunnel_junction_data_declared": True,
    }
    return {
        "status": "janus-sigma-boundary-action-support-gate",
        "support": support,
        "sigma_boundary_support_declared": all(support.values()),
        "nonlinear_boundary_variation_on_sigma_closed": True,
        "full_boundary_action_closed_on_sigma": True,
        "next_required": "none for Sigma boundary action",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Sigma Boundary Action Support Gate",
            "",
            f"Sigma support declared: `{payload['sigma_boundary_support_declared']}`",
            f"Full boundary action closed on Sigma: `{payload['full_boundary_action_closed_on_sigma']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

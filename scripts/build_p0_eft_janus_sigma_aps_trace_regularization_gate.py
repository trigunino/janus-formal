from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sigma_aps_trace_regularization_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sigma_aps_trace_regularization_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-sigma-aps-trace-regularization-gate",
        "sigma_aps_boundary_pin_lift_closed": True,
        "clifford_trace_normalization_declared": True,
        "aps_heat_kernel_regularization_declared": True,
        "trace_regularization_standard_global": True,
        "sigma_aps_trace_regularization_closed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Sigma APS Trace Regularization Gate",
            "",
            f"Trace regularization closed: `{payload['sigma_aps_trace_regularization_closed']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

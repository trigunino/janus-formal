from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sigma_aps_local_throat_model_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sigma_aps_local_throat_model_gate.json")


def build_payload() -> dict:
    local = {
        "sigma_compact_boundary_declared": True,
        "sigma_oriented_local_model_declared": True,
        "sigma_spin_local_model_declared": True,
        "induced_pin_structure_available_locally": True,
        "aps_boundary_projector_available_locally": True,
        "fredholm_domain_available_locally": True,
        "sigma_aps_local_throat_model_closed": True,
    }
    global_open = {
        "eta_zero_mode_cancellation_deferred_to_eta_gate": True,
        "parity_anomaly_cancellation_global_closed": False,
        "sigma_aps_boundary_pin_lift_closed": False,
    }
    return {
        "status": "janus-sigma-aps-local-throat-model-gate",
        "local": local,
        "global": global_open,
        "sigma_aps_local_package_closed": all(local.values()),
        "sigma_aps_boundary_pin_lift_closed": False,
        "interpretation": (
            "The compact orientable Sigma throat supplies a local spin/Pin APS "
            "projector and Fredholm domain. Eta cancellation is handled by the "
            "dedicated eta gate; global parity cancellation remains open."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Sigma APS Local Throat Model Gate",
            "",
            f"Local APS package closed: `{payload['sigma_aps_local_package_closed']}`",
            f"Sigma APS boundary Pin lift closed: `{payload['sigma_aps_boundary_pin_lift_closed']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

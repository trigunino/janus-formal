from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.write_p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge import (
    build_payload as build_dimensionless_density,
)
from scripts.write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation import (
    build_payload as build_effective_closure,
)
from scripts.write_p0_eft_janus_z2_sigma_hubble_volume_noether_density import (
    build_payload as build_hubble_volume_density,
)
from scripts.write_p0_eft_janus_z2_sigma_projected_charge_from_occupation_state import (
    build_payload as build_projected_charge,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_initial_state_pipeline_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_initial_state_pipeline_gate.json")


def build_payload() -> dict:
    closure = build_effective_closure()
    charge = build_projected_charge()
    density = build_dimensionless_density()
    hubble_density = build_hubble_volume_density()
    stages = {
        "effective_closure": closure["effective_closure_ready"],
        "projected_charge": charge["gate_passed"],
        "dimensionless_noether_density": density["gate_passed"],
        "hubble_volume_noether_density": hubble_density["gate_passed"],
    }
    return {
        "status": "janus-z2-sigma-effective-initial-state-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "effective_initial_state",
        "stages": stages,
        "stage_payloads": {
            "effective_closure": closure,
            "projected_charge": charge,
            "dimensionless_noether_density": density,
            "hubble_volume_noether_density": hubble_density,
        },
        "pipeline_ready": all(stages.values()),
        "full_no_fit_prediction_ready": False,
        "primary_blocker": "none"
        if all(stages.values())
        else next(name for name, ready in stages.items() if not ready),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective Initial State Pipeline Gate",
        "",
        f"Pipeline ready: `{payload['pipeline_ready']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Stages",
    ]
    lines.extend(f"- `{name}`: `{ready}`" for name, ready in payload["stages"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

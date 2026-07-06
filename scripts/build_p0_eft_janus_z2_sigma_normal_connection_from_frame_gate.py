from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_normal_connection import (
    load_and_materialize_normal_connection,
)


INPUT_PATH = Path("outputs/active_z2_sigma/normal_connection_frame_primitives.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/normal_connection_omega_perp_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_connection_from_frame_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_connection_from_frame_gate.json")


def build_payload(input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-normal-connection-from-frame-gate",
            "active_core": "Z2_tunnel_Sigma",
            "input_path": str(input_path),
            "output_path": str(output_path),
            "input_manifest_present": False,
            "normal_connection_ready": False,
            "omega_perp_from_active_normal_frame": False,
            "writes_active_output": False,
            "gate_passed": False,
            "blocker": "normal_connection_frame_primitives_missing",
        }

    payload = load_and_materialize_normal_connection(input_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    payload.update(
        {
            "status": "janus-z2-sigma-normal-connection-from-frame-gate",
            "input_path": str(input_path),
            "output_path": str(output_path),
            "input_manifest_present": True,
            "writes_active_output": True,
            "gate_passed": True,
        }
    )
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Normal Connection From Frame Gate",
                "",
                f"Input manifest present: `{payload['input_manifest_present']}`",
                f"Normal connection ready: `{payload['normal_connection_ready']}`",
                f"Omega from active normal frame: `{payload['omega_perp_from_active_normal_frame']}`",
                f"Gate passed: `{payload['gate_passed']}`",
                f"Blocker: `{payload.get('blocker', 'none')}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

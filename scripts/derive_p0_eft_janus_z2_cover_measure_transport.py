from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_cover_measure_transport import load_and_derive_measure_transport


INPUT_PATH = Path("outputs/active_z2_cover/measure_transport_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_cover/measure_transport.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_measure_transport.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_measure_transport.json")


def build_payload(input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-cover-measure-transport",
            "active_core": "JanusZ2CoverMasterAction",
            "input_path": str(input_path),
            "output_path": str(output_path),
            "input_manifest_present": False,
            "measure_transport_ready": False,
            "full_no_fit_prediction_ready": False,
            "gate_passed": False,
            "primary_blocker": "measure_transport_inputs_missing",
        }
    payload = load_and_derive_measure_transport(input_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    payload.update(
        {
            "status": "janus-z2-cover-measure-transport",
            "input_path": str(input_path),
            "output_path": str(output_path),
            "input_manifest_present": True,
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
                "# Janus Z2 Cover Measure Transport",
                "",
                f"Input present: `{payload['input_manifest_present']}`",
                f"Measure transport ready: `{payload['measure_transport_ready']}`",
                f"Primary blocker: `{payload.get('primary_blocker', 'none')}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

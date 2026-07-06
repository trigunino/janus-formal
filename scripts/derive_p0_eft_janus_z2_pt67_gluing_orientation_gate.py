from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_pt67_gluing_orientation import pt67_gluing_orientation_payload

JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_pt67_gluing_orientation_gate.json")


def build_payload() -> dict:
    return pt67_gluing_orientation_payload()


def write_outputs() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))

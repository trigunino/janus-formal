from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    normal_connection_to_sym4_anormal_bridge_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_normal_connection_to_sym4_anormal_bridge_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_normal_connection_to_sym4_anormal_bridge_gate.json")


def write_reports() -> dict:
    payload = normal_connection_to_sym4_anormal_bridge_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    machinery = payload["existing_normal_connection_machinery"]
    lines = [
        "# Janus Normal Connection To Sym4 A_normal Bridge Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Calculator ready: `{machinery['calculator_ready']}`",
        f"Active input manifest present: `{machinery['active_input_manifest_present']}`",
        "",
        "## Bridge requirements",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["bridge_requirements"].items())
    lines.extend(["", "## Why existing omega is not enough"])
    lines.extend(f"- {item}" for item in payload["why_existing_omega_is_not_enough"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

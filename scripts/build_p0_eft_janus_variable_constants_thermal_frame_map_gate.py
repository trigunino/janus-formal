from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    variable_constants_thermal_frame_map_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_variable_constants_thermal_frame_map_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_variable_constants_thermal_frame_map_gate.json")


def write_reports() -> dict:
    payload = variable_constants_thermal_frame_map_payload()
    payload["gate_passed"] = all(payload["checks"].values())
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Variable-Constants Thermal Frame Map Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Inputs",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["inputs"].items())
    lines.extend(["", "## Solution"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["solution"].items())
    lines.extend(["", "## Checks"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["checks"].items())
    lines.extend(["", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

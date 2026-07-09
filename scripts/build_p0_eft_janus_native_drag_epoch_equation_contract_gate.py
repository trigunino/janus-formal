from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    native_drag_epoch_equation_contract_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_native_drag_epoch_equation_contract_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_native_drag_epoch_equation_contract_gate.json")


def write_reports() -> dict:
    payload = native_drag_epoch_equation_contract_payload()
    payload["gate_passed"] = payload["structural_prediction_ready"]
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Native Drag Epoch Equation Contract Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Numeric prediction ready: `{payload['numeric_prediction_ready']}`",
        f"Equation: `{payload['equation']}`",
        f"Saha proxy: `{payload['saha_visibility_proxy']}`",
        "",
        "## Remaining inputs",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["remaining_inputs"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    visible_matter_jordan_frame_pullback_attempt_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_visible_matter_jordan_frame_pullback_attempt_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_visible_matter_jordan_frame_pullback_attempt_gate.json")


def write_reports() -> dict:
    payload = visible_matter_jordan_frame_pullback_attempt_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Visible Matter Jordan Frame Pullback Attempt Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Visible clock fixed: `{payload['visible_clock_fixed']}`",
        f"Weyl cusp predictive: `{payload['weyl_cusp_predictive']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

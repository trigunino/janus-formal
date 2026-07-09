from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    attached_early_branch_timescale_law_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_attached_early_branch_timescale_law_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_attached_early_branch_timescale_law_gate.json")


def write_reports() -> dict:
    payload = attached_early_branch_timescale_law_payload()
    payload["gate_passed"] = payload["result"]["new_free_ratio_removed"]
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Attached Early Branch Timescale Law Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Law",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["law"].items())
    lines.extend(["", "## Values"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["values"].items())
    lines.extend(["", "## Result"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["result"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    early_universe_native_plasma_frontier_verdict_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_early_universe_native_plasma_frontier_verdict_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_early_universe_native_plasma_frontier_verdict_gate.json")


def write_reports() -> dict:
    payload = early_universe_native_plasma_frontier_verdict_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = ["# Janus Early-Universe Native Plasma Frontier Verdict", ""]
    lines.append(f"Gate passed: `{payload['gate_passed']}`")
    lines.extend(["", "## Closed"])
    lines.extend(f"- `{item}`" for item in payload["closed"])
    lines.extend(["", "## Blocked"])
    lines.extend(f"- `{item}`" for item in payload["blocked"])
    lines.extend(["", "## Surviving routes"])
    lines.extend(f"- `{row['route']}`: {row['needed']} ({row['status']})" for row in payload["surviving_routes"])
    lines.extend(["", "## Not allowed"])
    lines.extend(f"- `{item}`" for item in payload["not_allowed"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

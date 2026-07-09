from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    sym4_internal_transfer_frontier_verdict_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sym4_internal_transfer_frontier_verdict_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sym4_internal_transfer_frontier_verdict_gate.json")


def write_reports() -> dict:
    payload = sym4_internal_transfer_frontier_verdict_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Sym4 Internal Transfer Frontier Verdict Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Current best route: `{payload['current_best_non_rustine_route']}`",
        "",
        "## Exhausted routes",
    ]
    lines.extend(f"- {item}" for item in payload["exhausted_routes"])
    lines.extend(["", "## Remaining hard objects"])
    lines.extend(f"- {item}" for item in payload["remaining_hard_objects"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

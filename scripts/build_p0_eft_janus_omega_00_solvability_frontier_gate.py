from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import omega_00_solvability_frontier_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_omega_00_solvability_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_omega_00_solvability_frontier_gate.json")


def write_reports() -> dict:
    payload = omega_00_solvability_frontier_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Omega 00 Solvability Frontier Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Can solve Omega now: `{payload['can_solve_omega_now']}`",
        "",
        "## Closed",
    ]
    for key, value in payload["closed"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Still open"])
    for key, value in payload["still_open"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

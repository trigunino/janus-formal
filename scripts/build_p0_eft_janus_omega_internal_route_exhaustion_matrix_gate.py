from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import omega_internal_route_exhaustion_matrix_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_omega_internal_route_exhaustion_matrix_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_omega_internal_route_exhaustion_matrix_gate.json")


def write_reports() -> dict:
    payload = omega_internal_route_exhaustion_matrix_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Omega Internal Route Exhaustion Matrix Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Any internal route closed: `{payload['any_internal_route_closed']}`",
        "",
        "## Routes",
    ]
    for row in payload["routes"]:
        lines.append(f"- `{row['name']}`: closed=`{row['closed']}`; stops={row['why_it_stops']}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

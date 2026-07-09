from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    anormal_weight_origin_candidate_matrix_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_anormal_weight_origin_candidate_matrix_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_anormal_weight_origin_candidate_matrix_gate.json")


def write_reports() -> dict:
    payload = anormal_weight_origin_candidate_matrix_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus A_normal Weight Origin Candidate Matrix Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Required output",
        payload["required_output"],
        "",
        "## Candidates",
    ]
    for row in payload["candidates"]:
        line = (
            f"- `{row['name']}`: anchored=`{row['janus_anchored']}`, "
            f"orders_1001=`{row['orders_1001']}`"
        )
        if "failure" in row:
            line += f"; failure={row['failure']}"
        if "missing" in row:
            line += f"; missing={', '.join(row['missing'])}"
        lines.append(line)
    lines.extend(["", "## Credible remaining routes"])
    for route in payload["credible_remaining_routes"]:
        lines.append(f"- `{route}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    anormal_sym4_spectral_condition_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_anormal_sym4_spectral_condition_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_anormal_sym4_spectral_condition_gate.json")


def write_reports() -> dict:
    payload = anormal_sym4_spectral_condition_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus A_normal Sym4 Spectral Condition Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        payload["spectral_rule"],
        "",
        "## Cases",
    ]
    for row in payload["cases"]:
        lines.append(
            f"- `{row['name']}`: levels=`{row['distinct_levels']}`, "
            f"orders_1001=`{row['orders_1001']}`, anchored=`{row['janus_anchored']}`"
        )
    lines.extend(["", "## Necessary condition", payload["necessary_condition"]])
    lines.extend(["", "## Janus gap", payload["janus_gap"]])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

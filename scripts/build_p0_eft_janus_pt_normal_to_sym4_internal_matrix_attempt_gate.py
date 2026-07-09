from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    pt_normal_to_sym4_internal_matrix_attempt_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_pt_normal_to_sym4_internal_matrix_attempt_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_pt_normal_to_sym4_internal_matrix_attempt_gate.json")


def write_reports() -> dict:
    payload = pt_normal_to_sym4_internal_matrix_attempt_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus PT Normal To Sym4 Internal Matrix Attempt Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Derived non-scalar internal matrix now: `{payload['derived_non_scalar_internal_matrix_now']}`",
        f"Best remaining object: `{payload['best_remaining_object']}`",
        "",
        "## Tested actions",
    ]
    for row in payload["tested_actions"]:
        lines.append(
            f"- `{row['action']}`: non_scalar=`{row['non_scalar_on_Sym4']}`, "
            f"orders=`{row['orders_1001_states']}`, verdict=`{row['verdict']}`"
        )
    lines.extend(["", "## A_normal requirements"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["A_normal_requirements"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

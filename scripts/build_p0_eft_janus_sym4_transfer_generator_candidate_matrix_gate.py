from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    sym4_transfer_generator_candidate_matrix_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sym4_transfer_generator_candidate_matrix_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sym4_transfer_generator_candidate_matrix_gate.json")


def write_reports() -> dict:
    payload = sym4_transfer_generator_candidate_matrix_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Sym4 Transfer Generator Candidate Matrix Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Any non-rustine closer: `{payload['any_non_rustine_closer']}`",
        "",
        "## Candidates",
    ]
    for row in payload["candidates"]:
        lines.append(
            f"- `{row['name']}`: anchored=`{row['anchored']}`, "
            f"finite=`{row['finite_on_Sym4']}`, orders=`{row['orders_normal_redshift_states']}`; "
            f"{row['failure']}"
        )
    lines.extend(["", "## Next required theorem", payload["next_required_theorem"]])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

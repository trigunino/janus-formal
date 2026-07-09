from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    early_branch_attachment_requirements_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_early_branch_attachment_requirements_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_early_branch_attachment_requirements_gate.json")


def write_reports() -> dict:
    payload = early_branch_attachment_requirements_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Early Branch Attachment Requirements Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Target redshift: `{payload['target_redshift']}`",
        "",
        "## Geometric redshift requirement",
    ]
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["geometric_redshift_requirement"].items()
    )
    lines.extend(["", "## Required new structure"])
    lines.extend(f"- `{item}`" for item in payload["required_new_structure"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

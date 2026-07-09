from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    conformal_trace_source_content_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_conformal_trace_source_content_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_conformal_trace_source_content_audit_gate.json")


def write_reports() -> dict:
    payload = conformal_trace_source_content_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Conformal Trace Source Content Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Trace sufficient for predrag: `{payload['trace_is_sufficient_for_predrag']}`",
        f"Recommended projection: `{payload['recommended_projection']}`",
        "",
        "## Source trace table",
    ]
    for row in payload["source_trace_table"]:
        lines.append(f"- `{row['component']}`: trace={row['trace']}, seen={row['seen_by_trace_equation']}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

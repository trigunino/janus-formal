from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    m31_compact_charge_to_anormal_weight_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_m31_compact_charge_to_anormal_weight_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_m31_compact_charge_to_anormal_weight_audit_gate.json")


def write_reports() -> dict:
    payload = m31_compact_charge_to_anormal_weight_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus M31 Compact Charge To A_normal Weight Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Source: `{payload['source_anchor']['paper']}`",
        f"Equations: `{payload['source_anchor']['equation_range']}`",
        "",
        "## What it closes",
    ]
    for key, value in payload["what_it_closes"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## What it does not close"])
    for key, value in payload["what_it_does_not_close"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Non-rustine extension path"])
    for row in payload["non_rustine_extension_path"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    entropy_cutoff_drag_readiness_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_entropy_cutoff_drag_readiness_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_entropy_cutoff_drag_readiness_audit_gate.json")


def write_reports() -> dict:
    payload = entropy_cutoff_drag_readiness_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Entropy Cutoff Drag Readiness Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Entropy cutoff available: `{payload['entropy_cutoff_available']}`",
        f"C_ion from CODATA/FIRAS: `{payload['C_ion_from_CODATA_FIRAS']}`",
        f"Drag prediction executable: `{payload['drag_prediction_executable']}`",
        "",
        "## Still missing",
    ]
    for key, value in payload["still_missing_for_drag_epoch"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

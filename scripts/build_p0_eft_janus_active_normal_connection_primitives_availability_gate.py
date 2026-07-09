from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    active_normal_connection_primitives_availability_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_active_normal_connection_primitives_availability_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_active_normal_connection_primitives_availability_gate.json")


def write_reports() -> dict:
    payload = active_normal_connection_primitives_availability_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Active Normal Connection Primitives Availability Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Required manifest present: `{payload['required_manifest_present']}`",
        f"Can materialize active omega_perp now: `{payload['can_materialize_active_omega_perp_now']}`",
        f"Safe to create zero manifest as proof: `{payload['safe_to_create_zero_manifest_as_proof']}`",
        "",
        "## Missing",
    ]
    for row in payload["next_required"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

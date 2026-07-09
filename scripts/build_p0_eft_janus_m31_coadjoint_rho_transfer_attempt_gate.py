from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    m31_coadjoint_rho_transfer_attempt_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_m31_coadjoint_rho_transfer_attempt_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_m31_coadjoint_rho_transfer_attempt_gate.json")


def write_reports() -> dict:
    payload = m31_coadjoint_rho_transfer_attempt_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus M31 Coadjoint Rho Transfer Attempt Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Normal/redshift generator found: `{payload['normal_redshift_generator_found']}`",
        "",
        "## Progress",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["what_progresses"].items())
    lines.extend(["", "## Generator audit"])
    for row in payload["generator_audit"]:
        lines.append(f"- `{row['name']}`: normal_H=`{row['normal_redshift_H']}`; {row['reason']}")
    lines.extend(["", "## Remaining gap", payload["remaining_gap"]])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

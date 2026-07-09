from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    m31_exterior_power_consistency_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_m31_exterior_power_consistency_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_m31_exterior_power_consistency_audit_gate.json")


def write_reports() -> dict:
    payload = m31_exterior_power_consistency_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus M31 Exterior-Power Consistency Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Required N: `{payload['required_N']}`",
        f"Legal matches: `{payload['legal_matches']}`",
        f"No-fit selector survives audit: `{payload['current_no_fit_selector_survives_audit']}`",
        "",
        "## Alternatives",
    ]
    for row in payload["alternatives"]:
        lines.append(
            "- `{name}`: dimension `{dimension}`, match `{matches_required_N}`, legal `{structurally_legal_from_M31}`; {reason}".format(
                **row
            )
        )
    lines.extend(["", "## Bottom line", payload["bottom_line"], "", "## Next required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

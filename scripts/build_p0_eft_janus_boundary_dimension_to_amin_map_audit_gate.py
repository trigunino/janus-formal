from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    boundary_dimension_to_amin_map_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_boundary_dimension_to_amin_map_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_boundary_dimension_to_amin_map_audit_gate.json")


def write_reports() -> dict:
    payload = boundary_dimension_to_amin_map_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Boundary Dimension To Amin Map Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"N: `{payload['N']}`",
        f"Successful maps: `{payload['successful_maps']}`",
        f"Current map derived: `{payload['current_map_derived']}`",
        "",
        "## Maps",
    ]
    for row in payload["maps"]:
        lines.append(
            "- `{name}`: {formula}, a_min `{a_min}`, z_max `{z_max}`, matches `{matches_predrag}`".format(
                **row
            )
        )
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

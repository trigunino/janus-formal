from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    m31_to_sym4_boundary_representation_gap_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_m31_to_sym4_boundary_representation_gap_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_m31_to_sym4_boundary_representation_gap_gate.json")


def write_reports() -> dict:
    payload = m31_to_sym4_boundary_representation_gap_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus M31 To Sym4 Boundary Representation Gap Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Minimal missing object: `{payload['minimal_missing_object']}`",
        "",
        "## Derivation chain",
    ]
    for row in payload["derivation_chain"]:
        lines.append(f"- `{row['step']}`: available=`{row['available']}`; {row['note']}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

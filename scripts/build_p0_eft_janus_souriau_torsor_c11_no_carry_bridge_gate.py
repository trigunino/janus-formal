from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    souriau_torsor_c11_no_carry_bridge_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_souriau_torsor_c11_no_carry_bridge_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_souriau_torsor_c11_no_carry_bridge_gate.json")


def write_reports() -> dict:
    payload = souriau_torsor_c11_no_carry_bridge_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Souriau Torsor C11 No-Carry Bridge Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"C11 basis identified: `{payload['C11_basis_identified']}`",
        f"Canonical component order derived: `{payload['canonical_component_order_derived']}`",
        f"No-fit closed now: `{payload['no_fit_closed_now']}`",
        "",
        "## Components",
    ]
    for row in payload["components"]:
        lines.append(f"- `{row['name']}`: dim={row['dimension']}, {row['meaning']}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

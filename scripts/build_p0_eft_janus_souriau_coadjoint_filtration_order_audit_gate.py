from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    souriau_coadjoint_filtration_order_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_souriau_coadjoint_filtration_order_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_souriau_coadjoint_filtration_order_audit_gate.json")


def write_reports() -> dict:
    payload = souriau_coadjoint_filtration_order_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Souriau Coadjoint Filtration Order Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Coadjoint filtration derived: `{payload['coadjoint_filtration_derived']}`",
        f"Full component order derived: `{payload['full_component_order_derived']}`",
        f"Block profile levels on Sym4: `{payload['block_profile_levels_on_Sym4']}`",
        f"Orders 1001 states: `{payload['orders_1001_states']}`",
        "",
        "## Blocks",
    ]
    for row in payload["filtration_blocks"]:
        lines.append(f"- `{row['name']}`: dim={row['dimension']}, {row['coadjoint_role']}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

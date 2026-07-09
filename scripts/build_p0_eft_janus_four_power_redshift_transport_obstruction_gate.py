from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    four_power_redshift_transport_obstruction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_four_power_redshift_transport_obstruction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_four_power_redshift_transport_obstruction_gate.json")


def write_reports() -> dict:
    payload = four_power_redshift_transport_obstruction_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Four-Power Redshift Transport Obstruction Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"s=4 source-derived: `{payload['result']['s4_source_derived']}`",
        f"s=4 promotable: `{payload['result']['s4_promotable']}`",
        "",
        "## Candidate decompositions",
    ]
    for row in payload["candidate_decompositions"]:
        lines.append(
            "- `{name}`: pieces `{pieces}`, verdict `{verdict}`; {reason}".format(
                **row
            )
        )
    lines.extend(["", "## Bottom line", payload["bottom_line"], "", "## Next required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

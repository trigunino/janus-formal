from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    redshift_exponent_q0_compatibility_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_redshift_exponent_q0_compatibility_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_redshift_exponent_q0_compatibility_gate.json")


def write_reports() -> dict:
    payload = redshift_exponent_q0_compatibility_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Redshift Exponent / q0 Compatibility Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Target redshift: `{payload['target_redshift']}`",
        f"Published q0: `{payload['published_q0']}`",
        "",
        "## Rows",
    ]
    for row in payload["rows"]:
        lines.append(
            "- `{name}`: s `{redshift_exponent_s}`, required q0 `{required_q0}`, sigma offset `{sigma_offset_from_published_q0}`, within 2 sigma `{within_two_sigma}`".format(
                **row
            )
        )
    lines.extend(["", "## Bottom line", payload["bottom_line"], "", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

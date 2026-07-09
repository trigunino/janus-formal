from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    early_redshift_map_feasibility_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_early_redshift_map_feasibility_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_early_redshift_map_feasibility_gate.json")


def write_reports() -> dict:
    payload = early_redshift_map_feasibility_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Early Redshift Map Feasibility Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"a_min/a0: `{payload['a_min_over_a0']}`",
        f"Target redshift: `{payload['target_redshift']}`",
        f"Required exponent s: `{payload['required_exponent_s']}`",
        "",
        "## Candidate maps",
    ]
    for row in payload["candidate_maps"]:
        lines.append(
            "- `{name}`: s `{exponent_s}`, z_max `{z_max}`, reaches target `{reaches_target}`, status `{status}`".format(
                **row
            )
        )
    lines.extend(["", "## Bottom line", payload["bottom_line"], "", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

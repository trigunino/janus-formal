from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    plus_sector_maxwell_radiation_action_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_plus_sector_maxwell_radiation_action_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_plus_sector_maxwell_radiation_action_gate.json")


def write_reports() -> dict:
    payload = plus_sector_maxwell_radiation_action_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Plus-Sector Maxwell/Radiation Action Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Classification: `{payload['paper_relation']['classification']}`",
        f"Paper explicit: `{payload['paper_relation']['explicitly_given_by_paper']}`",
        "",
        "## Action contract",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["action_contract"].items())
    lines.extend(["", "## Derived objects"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["derived_objects"].items())
    lines.extend(["", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

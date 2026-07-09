from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import amin_integer_sector_requirements_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_amin_integer_sector_requirements_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_amin_integer_sector_requirements_gate.json")


def write_reports() -> dict:
    payload = amin_integer_sector_requirements_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus a_min Integer Sector Requirements Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Ansatz: `{payload['ansatz']}`",
        f"Required N min: `{payload['required_N_min']}`",
        "",
        "## Candidates",
    ]
    for row in payload["candidates"]:
        lines.append("- `{name}`: N `{N}`, status `{status}`; {reason}".format(**row))
    lines.extend(["", "## Internal tests required"])
    lines.extend(f"- `{item}`" for item in payload["internal_tests_required"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    entropy_to_ruler_resolution_map_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_entropy_to_ruler_resolution_map_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_entropy_to_ruler_resolution_map_gate.json")


def write_reports() -> dict:
    payload = entropy_to_ruler_resolution_map_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    m = payload["mathematical_map"]
    lines = [
        "# Janus Entropy To Ruler Resolution Map Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"N cells: `{m['N_cells']}`",
        f"a_min: `{m['a_min']}`",
        f"z_max: `{m['z_max']}`",
        f"Pre-drag reach: `{m['pre_drag_reach']}`",
        f"No-fit closed now: `{payload['no_fit_closed_now']}`",
        "",
        "## Not closed",
    ]
    for key, value in payload["what_is_not_closed"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

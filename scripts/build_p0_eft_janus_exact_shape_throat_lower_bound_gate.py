from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    exact_shape_throat_lower_bound_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_exact_shape_throat_lower_bound_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_exact_shape_throat_lower_bound_gate.json")


def write_reports() -> dict:
    payload = exact_shape_throat_lower_bound_payload()
    payload["gate_passed"] = payload["consequences"]["nonzero_lower_bound_for_sound_horizon"]
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Exact Shape Throat Lower-Bound Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"q0: `{payload['q0']}`",
        f"a_min/a0: `{payload['a_min_over_a0']}`",
        f"z_max: `{payload['z_max']}`",
        "",
        "## Consequences",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["consequences"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"], "", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

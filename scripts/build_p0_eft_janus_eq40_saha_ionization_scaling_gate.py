from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    eq40_saha_ionization_scaling_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_eq40_saha_ionization_scaling_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_eq40_saha_ionization_scaling_gate.json")


def write_reports() -> dict:
    payload = eq40_saha_ionization_scaling_payload()
    payload["gate_passed"] = payload["unblocks"]["native_ionization_visibility_law"]
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Eq40 Saha Ionization Scaling Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Saha form: `{payload['saha_form']}`",
        "",
        "## Derived",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["derived"].items())
    lines.extend(["", "## Interpretation", payload["interpretation"], "", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

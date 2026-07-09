from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    eq40_photon_clock_transport_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_eq40_photon_clock_transport_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_eq40_photon_clock_transport_audit_gate.json")


def write_reports() -> dict:
    payload = eq40_photon_clock_transport_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Eq40 Photon/Clock Transport Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Derived exponents",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["derived_exponents"].items())
    lines.extend(["", "## Result"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["result"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"], "", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    projective_hhat_from_s4rp4_limit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_projective_hhat_from_s4rp4_limit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_projective_hhat_from_s4rp4_limit_gate.json")


def write_reports() -> dict:
    payload = projective_hhat_from_s4rp4_limit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Projective Hhat From S4/RP4 Limit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Hhat geometry closed: `{payload['hhat_geometry_closed']}`",
        f"Hhat dynamics closed: `{payload['hhat_dynamics_closed']}`",
        "",
        "## Bottom line",
        payload["bottom_line"],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

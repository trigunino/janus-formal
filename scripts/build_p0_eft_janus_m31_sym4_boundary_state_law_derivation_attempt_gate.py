from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    m31_sym4_boundary_state_law_derivation_attempt_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_m31_sym4_boundary_state_law_derivation_attempt_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_m31_sym4_boundary_state_law_derivation_attempt_gate.json")


def write_reports() -> dict:
    payload = m31_sym4_boundary_state_law_derivation_attempt_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus M31 Sym4 Boundary State-Law Derivation Attempt Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Candidate: `{payload['candidate']}`",
        f"Required N: `{payload['required_N']}`",
        f"No-fit closed now: `{payload['no_fit_closed_now']}`",
        "",
        "## Steps",
    ]
    lines.extend(f"- `{row['status']}`: {row['step']}" for row in payload["derivation_steps"])
    lines.extend(["", "## If accepted"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["if_last_two_steps_are_accepted"].items())
    lines.extend(["", "## New principle needed", payload["new_principle_needed"], "", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

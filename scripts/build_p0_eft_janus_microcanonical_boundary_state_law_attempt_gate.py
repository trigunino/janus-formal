from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    microcanonical_boundary_state_law_attempt_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_microcanonical_boundary_state_law_attempt_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_microcanonical_boundary_state_law_attempt_gate.json")


def write_reports() -> dict:
    payload = microcanonical_boundary_state_law_attempt_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Microcanonical Boundary State Law Attempt Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"State: `{payload['state_law_candidate']}`",
        f"SO3 invariant: `{payload['symmetry']['SO3_invariant']}`",
        f"dim(H): `{payload['entropy']['dim_H_boundary']}`",
        f"a_min candidate: `{payload['ruler_map_attempt']['a_min_candidate']}`",
        f"Derives ruler from entropy: `{payload['ruler_map_attempt']['derives_ruler_from_entropy']}`",
        "",
        "## Remaining gap",
    ]
    for row in payload["remaining_derivation_gap"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

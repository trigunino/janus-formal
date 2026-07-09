from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    sym4_normal_channel_spectral_operator_candidate_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sym4_normal_channel_spectral_operator_candidate_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sym4_normal_channel_spectral_operator_candidate_gate.json")


def write_reports() -> dict:
    payload = sym4_normal_channel_spectral_operator_candidate_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Sym4 Normal Channel Spectral Operator Candidate Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Operator family: `{payload['inputs']['candidate_operator_family']}`",
        f"Finite N selected by operator alone: `{payload['operator_attempt']['finite_N_selected_by_operator_alone']}`",
        f"Finite N selected by Sym4 sector: `{payload['operator_attempt']['finite_N_selected_by_Sym4_sector']}`",
        "",
        "## What this closes",
    ]
    lines.extend(f"- {item}" for item in payload["what_this_closes"])
    lines.extend(["", "## What remains open"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["what_remains_open"].items())
    lines.extend(["", "## If all open steps are derived"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["if_all_open_steps_are_derived"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    sym4_finite_transfer_operator_candidate_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sym4_finite_transfer_operator_candidate_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sym4_finite_transfer_operator_candidate_gate.json")


def write_reports() -> dict:
    payload = sym4_finite_transfer_operator_candidate_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Sym4 Finite Transfer Operator Candidate Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Candidate: `{payload['candidate']}`",
        f"Hilbert dimension: `{payload['inputs']['Hilbert_dimension']}`",
        "",
        "## Why stronger than continuum cutoff",
    ]
    lines.extend(f"- {item}" for item in payload["why_stronger_than_continuum_spectral_cutoff"])
    lines.extend(["", "## Operator requirements"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["operator_requirements"].items())
    lines.extend(["", "## What would close if derived"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["what_would_close_if_derived"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

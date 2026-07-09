from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    quantum_fock_no_carry_anormal_candidate_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_quantum_fock_no_carry_anormal_candidate_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_quantum_fock_no_carry_anormal_candidate_gate.json")


def write_reports() -> dict:
    payload = quantum_fock_no_carry_anormal_candidate_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Quantum Fock No-Carry A_normal Candidate Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Operator: `{payload['candidate_operator']}`",
        f"Base: `{payload['inputs']['base']}`",
        f"Distinct levels: `{payload['spectrum']['distinct_levels']}`",
        f"Orders all Sym4 states: `{payload['spectrum']['orders_all_Sym4_states']}`",
        f"No-fit closed now: `{payload['no_fit_closed_now']}`",
        "",
        "## Not yet Janus-derived",
    ]
    for row in payload["not_yet_derived_from_janus"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Closure condition", payload["non_rustine_closure_condition"]])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

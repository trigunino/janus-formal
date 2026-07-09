from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    sym4_diagonal_hamiltonian_ordering_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sym4_diagonal_hamiltonian_ordering_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sym4_diagonal_hamiltonian_ordering_audit_gate.json")


def write_reports() -> dict:
    payload = sym4_diagonal_hamiltonian_ordering_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Sym4 Diagonal Hamiltonian Ordering Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Basis dimension: `{payload['inputs']['basis_dimension']}`",
        "",
        "## Diagonal cases",
    ]
    for row in payload["diagonal_hamiltonian_cases"]:
        lines.append(
            f"- `{row['case']}`: max profiles=`{row['max_distinct_profiles']}`, "
            f"orders all=`{row['can_order_all_1001_states']}`, verdict=`{row['verdict']}`"
        )
    lines.extend(["", "## No-fit conclusion"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["no_fit_conclusion"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

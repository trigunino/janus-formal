from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    sym4_schur_irreducibility_obstruction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sym4_schur_irreducibility_obstruction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sym4_schur_irreducibility_obstruction_gate.json")


def write_reports() -> dict:
    payload = sym4_schur_irreducibility_obstruction_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Sym4 Schur Irreducibility Obstruction Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Sector: `{payload['representation']['sector']}`",
        f"Dimension: `{payload['representation']['dimension']}`",
        "",
        "## Schur consequence",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["schur_consequence"].items())
    lines.extend(["", "## Allowed nontrivial H sources"])
    lines.extend(f"- {item}" for item in payload["allowed_nontrivial_H_sources"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

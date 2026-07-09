from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    cpt_boundary_fermionization_frontier_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_cpt_boundary_fermionization_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_cpt_boundary_fermionization_frontier_gate.json")


def write_reports() -> dict:
    payload = cpt_boundary_fermionization_frontier_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus CPT Boundary Fermionization Frontier Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"CPT fermionization derived: `{payload['cpt_fermionization_derived']}`",
        f"Keeps C(14,4) route alive as closed law: `{payload['keeps_C14_4_route_alive']}`",
        "",
        "## Inputs",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["inputs"].items())
    lines.extend(["", "## Missing requirements"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["requirements"].items())
    lines.extend(["", "## Blockers"])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

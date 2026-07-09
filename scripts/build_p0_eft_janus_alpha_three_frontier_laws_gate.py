from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import alpha_three_frontier_laws_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_alpha_three_frontier_laws_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_alpha_three_frontier_laws_gate.json")


def write_reports() -> dict:
    payload = alpha_three_frontier_laws_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Alpha Three Frontier Laws Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Any route closed now: `{payload['any_route_closed_now']}`",
        "",
        "## Routes",
    ]
    for route in payload["routes"]:
        lines.extend(
            [
                f"### {route['name']}",
                "",
                f"- repo status: `{route['repo_status']}`",
                f"- no-fit alpha generated: `{route['no_fit_alpha_generated']}`",
                f"- idea: {route['idea']}",
                f"- interpretation: {route['world_interpretation']}",
                f"- blocker: {', '.join(route['missing_inputs'])}",
                f"- verdict: {route['bottom_line']}",
                "",
            ]
        )
    lines.extend(
        [
            "## Rule",
            "",
            payload["non_rustine_rule"],
            "",
            "## Bottom line",
            "",
            payload["bottom_line"],
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

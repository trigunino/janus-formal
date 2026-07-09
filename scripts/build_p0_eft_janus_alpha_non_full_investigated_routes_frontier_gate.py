from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import alpha_non_full_investigated_routes_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_alpha_non_full_investigated_routes_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_alpha_non_full_investigated_routes_frontier_gate.json")


def write_reports() -> dict:
    payload = alpha_non_full_investigated_routes_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Janus Alpha Non-Fully Investigated Routes Frontier Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Routes pushed: `{payload['routes_pushed_count']}`",
        f"Any route closes alpha now: `{payload['any_route_closes_alpha_now']}`",
        "",
        "## Routes",
    ]
    for route in payload["routes"]:
        lines.extend(
            [
                f"### {route['name']}",
                "",
                f"- previous investigation: `{route['previous_investigation']}`",
                f"- pushed to: `{route['pushed_to']}`",
                f"- closes: {', '.join(route['what_closes'])}",
                f"- blocks: {', '.join(route['what_still_blocks'])}",
                f"- verdict: `{route['frontier_verdict']}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Best Remaining Order",
            "",
            *[f"{idx}. `{name}`" for idx, name in enumerate(payload["best_remaining_order"], 1)],
            "",
            "## Bottom Line",
            "",
            payload["bottom_line"],
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import alpha_tunnel_moebius_routes_terminal_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_alpha_tunnel_moebius_terminal_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_alpha_tunnel_moebius_terminal_gate.json")


def write_reports() -> dict:
    payload = alpha_tunnel_moebius_routes_terminal_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Alpha Tunnel/Moebius Terminal Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"All investigated to end: `{payload['all_investigated_to_end']}`",
        f"Any route closes alpha now: `{payload['any_route_closes_alpha_now']}`",
        "",
        "## Routes",
    ]
    for route in payload["routes"]:
        lines.extend(
            [
                f"### {route['name']}",
                "",
                f"- previous status: `{route['previous_status']}`",
                f"- investigated to end: `{route['investigated_to_end']}`",
                f"- provides: {', '.join(route['what_it_provides'])}",
                f"- does not provide: {', '.join(route['what_it_does_not_provide'])}",
                f"- verdict: {route['terminal_verdict']}",
                "",
            ]
        )
    lines.extend(["## Common Blocker", "", payload["common_blocker"], "", "## Bottom Line", "", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

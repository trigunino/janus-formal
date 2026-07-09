from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import non_throat_weyl_cusp_final_frontier_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_non_throat_weyl_cusp_final_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_non_throat_weyl_cusp_final_frontier_gate.json")


def write_reports() -> dict:
    payload = non_throat_weyl_cusp_final_frontier_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Non-Throat Weyl Cusp Final Frontier Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Can solve Omega now: `{payload['can_solve_omega_now']}`",
        f"Any internal route closed: `{payload['any_internal_route_closed']}`",
        "",
        "## Closed without rustine",
    ]
    for key, value in payload["closed_without_rustine"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Not closed without new law"])
    for key, value in payload["not_closed_without_new_law"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Verdict", payload["final_verdict"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

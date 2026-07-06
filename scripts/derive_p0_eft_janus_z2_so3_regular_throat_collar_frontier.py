from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_so3_regular_throat_collar import (
    regular_throat_collar_frontier_payload,
)


JSON_PATH = Path("outputs/active_z2_sigma/so3_regular_throat_collar_frontier.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_so3_regular_throat_collar_frontier.md")


def build_payload() -> dict:
    return regular_throat_collar_frontier_payload()


def write_outputs() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 SO(3) Regular Throat Collar Frontier",
        "",
        f"Radius law ready: `{payload['radius_law_ready']}`",
        f"Regular collar ready: `{payload['regular_collar_ready']}`",
        f"DeltaK derivable from collar: `{payload['DeltaK_derivable_from_collar']}`",
        "",
        "## Ansatz",
        "",
        f"`{payload['regular_collar_metric_ansatz']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))

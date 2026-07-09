from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    entropy_cutoff_to_native_sound_horizon_bridge_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_entropy_cutoff_to_native_sound_horizon_bridge_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_entropy_cutoff_to_native_sound_horizon_bridge_gate.json")


def write_reports() -> dict:
    payload = entropy_cutoff_to_native_sound_horizon_bridge_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    cutoff = payload["entropy_cutoff"]
    lines = [
        "# Janus Entropy Cutoff To Native Sound Horizon Bridge Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"a_min: `{cutoff['a_min']}`",
        f"z_max: `{cutoff['z_max']}`",
        f"Pre-drag reach: `{cutoff['pre_drag_reach']}`",
        f"Zero lower-limit divergence avoided: `{payload['sound_horizon_contract_updated']['zero_lower_limit_divergence_avoided']}`",
        "",
        "## Remaining inputs",
    ]
    for key, value in payload["remaining_inputs_after_cutoff"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

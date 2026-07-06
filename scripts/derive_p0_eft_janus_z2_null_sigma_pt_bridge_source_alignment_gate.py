from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_null_sigma_pt_bridge import (
    null_sigma_pt_bridge_source_alignment_payload,
)


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_null_sigma_pt_bridge_source_alignment_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_null_sigma_pt_bridge_source_alignment_gate.md")


def build_payload() -> dict:
    return null_sigma_pt_bridge_source_alignment_payload()


def write_outputs() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma / PT Bridge Source Alignment Gate",
        "",
        f"Branch: `{payload['branch']}`",
        f"Source alignment ready: `{payload['current_status']['source_alignment_ready']}`",
        f"Regular h/K pipeline allowed: `{payload['hard_separation_from_regular_sigma']['regular_h_ab_K_ab_pipeline_allowed']}`",
        f"Null boundary variables declared: `{payload['current_status']['null_boundary_variables_declared']}`",
        "",
        "## Source Anchors",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["source_anchors"].items())
    lines.extend(["", "## Required Null Formalism"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["required_null_formalism"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))

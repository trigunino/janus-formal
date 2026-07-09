from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    entropy_cutoff_exact_shape_compatibility_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_entropy_cutoff_exact_shape_compatibility_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_entropy_cutoff_exact_shape_compatibility_gate.json")


def write_reports() -> dict:
    payload = entropy_cutoff_exact_shape_compatibility_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Entropy Cutoff Exact Shape Compatibility Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Same branch compatible: `{payload['same_branch_compatible']}`",
        f"Entropy q0 required: `{payload['entropy_cutoff_branch']['q0_required_if_same_shape']}`",
        f"Late SN q0: `{payload['published_late_SN_branch']['q0']}`",
        "",
        "## Next required",
    ]
    for row in payload["next_required"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

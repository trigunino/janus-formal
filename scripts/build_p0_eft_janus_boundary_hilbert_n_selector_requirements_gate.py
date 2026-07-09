from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    boundary_hilbert_N_selector_requirements_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_boundary_hilbert_n_selector_requirements_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_boundary_hilbert_n_selector_requirements_gate.json")


def write_reports() -> dict:
    payload = boundary_hilbert_N_selector_requirements_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Boundary Hilbert N Selector Requirements Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Required N: `{payload['required_N']}`",
        f"Required CP1 spin j: `{payload['required_CP1_spin_j']}`",
        f"Required KKS/CS level: `{payload['required_KKS_or_CS_level']}`",
        "",
        "## Candidates",
    ]
    for row in payload["candidates"]:
        lines.append(
            "- `{name}`: {dimension_formula}, required `{required_value}`, Janus-derived `{janus_derived}`; blocker: {blocker}".format(
                **row
            )
        )
    lines.extend(["", "## Existing repo anchor"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["existing_repo_anchor"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"], "", "## Next required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

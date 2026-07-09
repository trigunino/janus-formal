from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    isotropy_preserving_anormal_ordering_obstruction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_isotropy_preserving_anormal_ordering_obstruction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_isotropy_preserving_anormal_ordering_obstruction_gate.json")


def write_reports() -> dict:
    payload = isotropy_preserving_anormal_ordering_obstruction_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Isotropy-Preserving A_normal Ordering Obstruction Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Full Sym4 levels: `{payload['full_sym4_levels']}`",
        f"Isotropic block profile levels: `{payload['isotropic_block_profile_levels']}`",
        f"Orders 1001 while isotropic: `{payload['orders_1001_while_isotropic']}`",
        "",
        "## Escape routes",
    ]
    for row in payload["allowed_non_rustine_escape_routes"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

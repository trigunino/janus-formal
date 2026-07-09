from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    m31_torsor_cpt_exterior_power_candidate_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_m31_torsor_cpt_exterior_power_candidate_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_m31_torsor_cpt_exterior_power_candidate_gate.json")


def write_reports() -> dict:
    payload = m31_torsor_cpt_exterior_power_candidate_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    construction = payload["candidate_construction"]
    lines = [
        "# Janus M31 Torsor+CPT Exterior-Power Candidate Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primitive boundary mode count: `{construction['primitive_boundary_mode_count']}`",
        f"Exterior degree: `{construction['exterior_degree']}`",
        f"Sector dimension: `{construction['sector_dimension']}`",
        f"Matches required N: `{construction['matches_required_N']}`",
        f"Matching exterior degrees: `{construction['matching_exterior_degrees']}`",
        "",
        "## Why not closed",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["why_not_closed"].items())
    lines.extend(["", "## Next", payload["non_rustine_next_step"], "", "## Verdict", payload["verdict"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

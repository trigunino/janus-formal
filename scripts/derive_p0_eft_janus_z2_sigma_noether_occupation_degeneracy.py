from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_projected_charge_reduction import (
    occupation_degeneracy_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_noether_occupation_degeneracy.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_noether_occupation_degeneracy.json"
)


def build_payload() -> dict:
    payload = occupation_degeneracy_payload()
    return {
        "status": "janus-z2-sigma-noether-occupation-degeneracy",
        **payload,
        "no_extension_charge_selection_exhausted": True,
        "full_projected_charge_ready": False,
        "next_required": [
            "derive a state-selection rule beyond Z2/Noether conservation",
            "or declare N_occ as initial state datum",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Noether Occupation Degeneracy",
        "",
        f"Tested occupations: `{payload['tested_occupations']}`",
        f"Projected charges: `{payload['projected_charges']}`",
        f"Topology selects unique occupation: `{payload['topology_selects_unique_occupation']}`",
        f"Charge conservation selects unique occupation: `{payload['charge_conservation_selects_unique_occupation']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

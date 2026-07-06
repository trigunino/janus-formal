from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_projected_charge_reduction import (
    z2_projected_charge_reduction_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_charge_reduction_to_occupation.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_charge_reduction_to_occupation.json"
)


def build_payload() -> dict:
    payload = z2_projected_charge_reduction_payload()
    return {
        "status": "janus-z2-sigma-projected-charge-reduction-to-occupation",
        **payload,
        "gate_passed": True,
        "next_required": [
            "derive global fermion occupation number N_occ",
            "or keep projected_baryon_number_charge_Z2Sigma as open initial datum",
        ],
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# Janus Z2/Sigma Projected Charge Reduction To Occupation",
            "",
            f"Projection weights free: `{payload['projection_weights_free']}`",
            f"General formula: `{payload['general_projected_charge_formula']}`",
            "Deck-invariant formula: "
            f"`{payload['deck_invariant_sector']['projected_charge_formula']}`",
            f"Full projected charge ready: `{payload['full_projected_charge_ready']}`",
            f"Primary blocker: `{payload['primary_blocker']}`",
            "",
            "## Next Required",
            *[f"- `{item}`" for item in payload["next_required"]],
        ]
    )


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

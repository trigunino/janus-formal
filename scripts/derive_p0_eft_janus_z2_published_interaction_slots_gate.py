from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_published_interaction_slots import published_interaction_slots_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_published_interaction_slots_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_published_interaction_slots_gate.json")


def build_payload() -> dict:
    payload = published_interaction_slots_payload()
    payload.update(
        {
            "status": "janus-z2-published-interaction-slots-gate",
            "gate_passed": True,
            "primary_blocker": "full_nonlinear_interaction_tensor_or_reduced_bianchi_closure",
            "next_required": [
                "choose a symmetry-reduced sector for interaction tensors",
                "derive D_plus RHS_plus = 0 and D_minus RHS_minus = 0 in that sector",
                "only then derive Sigma transport/source",
            ],
        }
    )
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published Interaction Slots Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Nonlinear interaction tensor available: `{payload['interaction_tensor_complete_nonlinear_form_available']}`",
        f"Reduced Bianchi closure ready: `{payload['reduced_bianchi_closure_ready']}`",
        f"Can transport to Sigma: `{payload['can_transport_to_sigma']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Equation Skeleton",
        f"- plus: `{payload['equation_skeleton']['plus']}`",
        f"- minus: `{payload['equation_skeleton']['minus']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

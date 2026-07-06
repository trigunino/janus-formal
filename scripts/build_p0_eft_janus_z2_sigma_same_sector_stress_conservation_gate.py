from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_dirac_matter_action_gate import (
    build_payload as build_matter_action_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_same_sector_stress_conservation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_same_sector_stress_conservation_gate.json")


def build_payload() -> dict:
    matter_action = build_matter_action_payload()
    plus_action_ready = bool(matter_action["closure"]["plus_matter_action_ready"])
    minus_action_ready = bool(matter_action["closure"]["minus_matter_action_ready"])
    closure = {
        "plus_minus_Dirac_matter_action_gate_imported": True,
        "plus_stress_tensor_declared_from_matter_action": True,
        "minus_stress_tensor_declared_from_matter_action": True,
        "plus_matter_diffeomorphism_Noether_identity_declared": True,
        "minus_matter_diffeomorphism_Noether_identity_declared": True,
        "cross_stress_excluded_from_same_sector_stress": True,
        "plus_matter_action_ready": plus_action_ready,
        "minus_matter_action_ready": minus_action_ready,
        "plus_matter_EOM_ready": plus_action_ready,
        "minus_matter_EOM_ready": minus_action_ready,
        "same_sector_plus_stress_conserved": plus_action_ready,
        "same_sector_minus_stress_conserved": minus_action_ready,
    }
    declared_ready = all(
        closure[key]
        for key in [
            "plus_minus_Dirac_matter_action_gate_imported",
            "plus_stress_tensor_declared_from_matter_action",
            "minus_stress_tensor_declared_from_matter_action",
            "plus_matter_diffeomorphism_Noether_identity_declared",
            "minus_matter_diffeomorphism_Noether_identity_declared",
            "cross_stress_excluded_from_same_sector_stress",
        ]
    )
    source_ready = all(closure.values())
    blockers = [key for key, value in closure.items() if not value]
    return {
        "status": "janus-z2-sigma-same-sector-stress-conservation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "same_sector_matter_action_noether_identity",
        "closure": closure,
        "declared_stress_conservation_layer_ready": declared_ready,
        "source_derivation_ready": source_ready,
        "gate_passed": declared_ready and source_ready,
        "primary_blocker": "none" if source_ready else blockers[0],
        "blockers": blockers,
        "formulas": {
            "plus": "matter EOM + plus matter diffeo Noether identity -> D_plus_nu T_plus^{mu nu}=0",
            "minus": "matter EOM + minus matter diffeo Noether identity -> D_minus_nu T_minus^{mu nu}=0",
            "scope": "same-sector T only; cross K/S terms remain in transport compatibility gates",
        },
        "upstream_matter_action_gate": {
            "gate": matter_action["status"],
            "plus_matter_action_ready": plus_action_ready,
            "minus_matter_action_ready": minus_action_ready,
            "primary_blockers": [
                key for key, value in matter_action["closure"].items() if not value
            ],
        },
        "feeds_conditional_closure_gate": {
            "same_sector_plus_stress_conserved": closure["same_sector_plus_stress_conserved"],
            "same_sector_minus_stress_conserved": closure["same_sector_minus_stress_conserved"],
        },
        "next_required": [
            "keep_cross_sector_transport_terms_separate",
            "then_feed_same_sector_stress_conservation_to_conditional_closure_gate",
        ],
        "interpretation": (
            "Same-sector stress conservation is a standard Noether consequence, but "
            "only after the plus/minus matter actions and matter EOM are active. It "
            "does not absorb or replace cross-sector transport terms."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Same-Sector Stress Conservation Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

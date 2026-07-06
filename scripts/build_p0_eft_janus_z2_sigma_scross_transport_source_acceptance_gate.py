from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_transport_map_derivation_gate import (
    build_payload as build_transport_payload,
)
from scripts.build_p0_janus_active_cross_action_acceptance_gate import (
    build_payload as build_cross_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scross_transport_source_acceptance_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scross_transport_source_acceptance_gate.json"
)


def build_payload() -> dict:
    cross = build_cross_payload()
    transport = build_transport_payload()
    closure = {
        "active_first_action_assembly_gate_imported": True,
        "transport_map_derivation_gate_imported": True,
        "published_Janus_field_equation_slot_available": bool(
            cross["m15_field_equation_action_available"]
        ),
        "independent_S_cross_functional_found": bool(cross["independent_scouple_found"]),
        "phi_L_variation_law_found": bool(
            cross["external_variational_transport_law_found"]
        ),
        "same_bridge_for_transport_and_Qcross_required": bool(
            transport["closure"]["Q_cross_uses_same_bridge"]
        ),
        "no_multiplier_route": True,
        "no_Qdet_Qcross_absorption": not bool(cross["uses_qdet_qcross_absorption"]),
        "no_observational_fit": not bool(cross["requires_observational_fit"]),
        "weak_selector_math_shape_closed": bool(
            cross["active_cross_action_derives_weak_selector"]
        ),
        "source_accepted_as_published_Janus": bool(
            cross["active_cross_action_source_accepted"]
        ),
        "explicit_new_axiom_allowed": bool(cross["can_adopt_as_explicit_new_axiom"]),
        "explicit_new_axiom_not_adopted": not bool(cross["new_axiom_adopted"]),
        "S_cross_transport_source_accepted": False,
    }
    ledger_keys = [
        "active_first_action_assembly_gate_imported",
        "transport_map_derivation_gate_imported",
        "published_Janus_field_equation_slot_available",
        "same_bridge_for_transport_and_Qcross_required",
        "no_multiplier_route",
        "no_Qdet_Qcross_absorption",
        "no_observational_fit",
        "weak_selector_math_shape_closed",
        "explicit_new_axiom_allowed",
    ]
    acceptance_keys = [
        "independent_S_cross_functional_found",
        "phi_L_variation_law_found",
        "same_bridge_for_transport_and_Qcross_required",
        "source_accepted_as_published_Janus",
        "explicit_new_axiom_not_adopted",
        "S_cross_transport_source_accepted",
    ]
    ledger_ready = all(closure[key] for key in ledger_keys)
    source_ready = ledger_ready and all(closure[key] for key in acceptance_keys)
    blockers = [key for key in acceptance_keys if not closure[key]]
    return {
        "status": "janus-z2-sigma-scross-transport-source-acceptance-gate",
        "route_status": "math_shape_closed_source_not_accepted",
        "closure": closure,
        "ledger_ready": ledger_ready,
        "source_acceptance_ready": source_ready,
        "gate_passed": source_ready,
        "primary_blocker": "none" if source_ready else blockers[0],
        "blockers": blockers,
        "upstream": {
            "active_cross_action_acceptance": {
                "gate": cross["status"],
                "math_valid": cross["active_cross_action_derives_weak_selector"],
                "source_accepted": cross["active_cross_action_source_accepted"],
                "new_axiom_allowed": cross["can_adopt_as_explicit_new_axiom"],
                "new_axiom_adopted": cross["new_axiom_adopted"],
            },
            "transport_map_derivation": {
                "gate": transport["status"],
                "same_bridge": transport["closure"]["Q_cross_uses_same_bridge"],
                "source_ready": transport["source_derivation_ready"],
            },
        },
        "next_required": [
            "find independent S_cross/S_couple functional in source",
            "derive phi/L variation law from that functional",
            "prove same bridge yields both stress transport and Q_cross",
            "then mark S_cross_transport_source_accepted",
        ],
        "verdict": (
            "The S_cross transport branch passes the no-fit/math-shape ledger, but it "
            "does not pass source acceptance as published Janus. It remains a usable "
            "new-axiom candidate only; the axiom is not adopted here."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma S_cross Transport Source Acceptance Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["verdict"],
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    lines.extend(["", "## Next Required"])
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

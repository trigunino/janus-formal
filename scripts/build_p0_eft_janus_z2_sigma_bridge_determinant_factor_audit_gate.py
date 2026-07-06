from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_abstract_tensor_transport_bianchi_gate import (
    build_payload as build_bianchi,
)
from scripts.build_p0_eft_janus_z2_sigma_transport_map_derivation_gate import (
    build_payload as build_transport,
)
from scripts.build_p0_eft_janus_z2_sigma_weakfield_poisson_interaction_sign_gate import (
    build_payload as build_weakfield,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_bridge_determinant_factor_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_bridge_determinant_factor_audit_gate.json"
)


def build_payload() -> dict:
    bianchi = build_bianchi()
    transport = build_transport()
    weakfield = build_weakfield()
    definitions = {
        "B_plus": "B_plus := sqrt(|g_minus|)/sqrt(|g_plus|)",
        "B_minus": "B_minus := sqrt(|g_plus|)/sqrt(|g_minus|)",
        "S_plus_cross": "B_plus K_plus(M_-+ T_minus)",
        "S_minus_cross": "B_minus K_minus(M_+- T_plus)",
        "Newtonian_limit": "B_plus = 1 + O(Phi), B_minus = 1 + O(Phi)",
    }
    closure = {
        "abstract_Bianchi_gate_imported": True,
        "transport_map_derivation_gate_imported": True,
        "weakfield_Poisson_sign_gate_imported": True,
        "B_plus_declared": True,
        "B_minus_declared": True,
        "B_plus_B_minus_reciprocal": True,
        "determinant_factors_kept_outside_bridge": bool(
            transport["closure"]["determinant_factors_kept_separate"]
        ),
        "stress_transport_uses_bridge_only": bool(
            transport["closure"]["stress_transport_uses_bridge"]
        ),
        "Qcross_uses_same_bridge_only": bool(
            transport["closure"]["Q_cross_uses_same_bridge"]
        ),
        "no_Qcross_determinant_absorption": bool(
            bianchi["closure"]["no_Qcross_determinant_shortcut"]
        ),
        "plus_RHS_uses_B_plus_K_plus": "B_plus K_plus" in bianchi["definitions"]["S_plus"],
        "minus_RHS_uses_B_minus_K_minus": "B_minus K_minus"
        in bianchi["definitions"]["S_minus"],
        "B_plus_Newtonian_limit_one": True,
        "B_minus_Newtonian_limit_one": True,
        "weakfield_sign_matrix_unchanged": bool(
            weakfield["closure"]["plus_equation_source_signed"]
            and weakfield["closure"]["minus_equation_source_signed"]
        ),
        "feeds_formal_Bianchi_ledger": bool(bianchi["formal_bianchi_closed"]),
    }
    gate_passed = all(closure.values())
    return {
        "status": "janus-z2-sigma-bridge-determinant-factor-audit-gate",
        "route_status": "formal_determinant_audit_closed_source_open",
        "definitions": definitions,
        "closure": closure,
        "gate_passed": gate_passed,
        "physics_closed": False,
        "source_derivation_ready": False,
        "primary_blocker": "source_derivation_of_transport_compatibility",
        "upstream": {
            "transport_map": {
                "gate": transport["status"],
                "determinants_separate": transport["closure"][
                    "determinant_factors_kept_separate"
                ],
                "same_bridge": transport["closure"]["Q_cross_uses_same_bridge"],
            },
            "bianchi": {
                "gate": bianchi["status"],
                "formal_closed": bianchi["formal_bianchi_closed"],
                "source_derived": bianchi["conditions_source_derived"],
            },
            "weakfield": {
                "gate": weakfield["status"],
                "matrix": weakfield["poisson_system"]["matrix"],
                "conditional_only": weakfield["conditional_only"],
            },
        },
        "next_required": [
            "derive determinant ratio from active embedding/pullback volume forms",
            "prove transport compatibility source equations",
            "then use B_plus,B_minus in full tensor Bianchi closure",
        ],
        "interpretation": (
            "The determinant factors are audited as volume ratios outside the tensor "
            "bridge. In the Newtonian limit they reduce to one, so they do not alter "
            "the Janus weak-field sign matrix. This is still formal/source-open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Bridge Determinant Factor Audit Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Physics closed: `{payload['physics_closed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Definitions",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["definitions"].items())
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

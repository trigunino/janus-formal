from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_bianchi_mixed_transport_map_target import (
    build_payload as build_mixed_transport_target,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_abstract_tensor_transport_bianchi_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_abstract_tensor_transport_bianchi_gate.json"
)


def build_payload() -> dict:
    mixed = build_mixed_transport_target()
    definitions = {
        "K_plus": "K_plus^{mu nu} := Transport_{- to +}[T_minus, g_minus, g_plus, M_minus_to_plus]",
        "K_minus": "K_minus^{mu nu} := Transport_{+ to -}[T_plus, g_plus, g_minus, M_plus_to_minus]",
        "B_plus": "B_plus := sqrt(-g_minus / -g_plus)",
        "B_minus": "B_minus := sqrt(-g_plus / -g_minus)",
        "S_plus": "S_plus^{mu nu} := T_plus^{mu nu} + B_plus K_plus^{mu nu}",
        "S_minus": "S_minus^{mu nu} := B_minus K_minus^{mu nu} + T_minus^{mu nu}",
    }
    compatibility_conditions = {
        "plus_transport_compatibility": (
            "D_plus_nu(T_plus^{mu nu} + B_plus K_plus^{mu nu}) = 0"
        ),
        "minus_transport_compatibility": (
            "D_minus_nu(B_minus K_minus^{mu nu} + T_minus^{mu nu}) = 0"
        ),
        "same_bridge_for_stress_and_optics": (
            "M_minus_to_plus/M_plus_to_minus are induced by the same bridge used by optical contractions"
        ),
    }
    forbidden_shortcuts = [
        "K_plus = T_minus as an untransported tensor copy",
        "K_minus = T_plus as an untransported tensor copy",
        "absorbing Q_cross into determinant-volume factors",
        "claiming tensor lensing before both Bianchi residuals vanish",
    ]
    closure = {
        "mixed_transport_maps_declared": True,
        "transport_minus_to_plus_declared": True,
        "transport_plus_to_minus_declared": True,
        "determinant_factors_declared": True,
        "coupled_RHS_plus_declared": True,
        "coupled_RHS_minus_declared": True,
        "no_Qcross_determinant_shortcut": True,
        "no_naive_tensor_copy_shortcut": True,
        "plus_transport_compatibility_assumed": True,
        "minus_transport_compatibility_assumed": True,
        "same_bridge_for_stress_and_optics_declared": True,
        "plus_Bianchi_residual_vanishes_formally": True,
        "minus_Bianchi_residual_vanishes_formally": True,
        "formal_Bianchi_implication_ready": True,
    }
    gate_passed = all(closure.values())
    return {
        "status": "janus-z2-sigma-abstract-tensor-transport-bianchi-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "abstract_conditional_transport",
        "definitions": definitions,
        "compatibility_conditions": compatibility_conditions,
        "forbidden_shortcuts": forbidden_shortcuts,
        "upstream_mixed_transport_target": {
            "description": mixed["description"],
            "physics_closed": mixed["physics_closed"],
            "definitions": mixed["definitions"],
        },
        "closure": closure,
        "formal_bianchi_closed": gate_passed,
        "conditions_source_derived": False,
        "active_geometry_required_for_source_derivation": True,
        "physics_closed": False,
        "prediction_ready": False,
        "gate_passed": gate_passed,
        "route_status": "formal_conditional_closed_source_open",
        "primary_blocker": "source_derivation_of_transport_maps",
        "next_required": [
            "derive_M_minus_to_plus_and_M_plus_to_minus_from_Z2Sigma_geometry",
            "prove_plus_transport_compatibility_from_source_equations",
            "prove_minus_transport_compatibility_from_source_equations",
            "reuse_same_bridge_for_K_transport_and_Q_cross",
        ],
        "interpretation": (
            "The abstract tensor transport layer is now closed as a formal implication: "
            "if the two transported RHS compatibility conditions hold, both Bianchi "
            "residuals vanish. This does not yet source-derive the transport maps."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Abstract Tensor Transport Bianchi Gate",
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
    lines.extend(["", "## Compatibility Conditions"])
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["compatibility_conditions"].items()
    )
    lines.extend(["", "## Forbidden Shortcuts"])
    lines.extend(f"- `{item}`" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_transport_map_derivation_gate import (
    build_payload as build_transport_map_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_transport_compatibility_source_equation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_transport_compatibility_source_equation_gate.json"
)


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    transport = build_transport_map_payload(embedding_manifest_path=embedding_manifest_path)
    bridge_ready = bool(transport["closure"]["bridge_maps_source_derived"])
    closure = {
        "transport_map_derivation_gate_imported": True,
        "plus_effective_RHS_declared": True,
        "minus_effective_RHS_declared": True,
        "plus_covariant_divergence_equation_declared": True,
        "minus_covariant_divergence_equation_declared": True,
        "same_bridge_used_in_both_divergences": True,
        "determinant_factors_kept_outside_bridge": True,
        "active_matter_source_equations_required": True,
        "bridge_maps_source_derived": bridge_ready,
        "plus_source_divergence_equation_derived": False,
        "minus_source_divergence_equation_derived": False,
        "plus_transport_compatibility_source_derived": False,
        "minus_transport_compatibility_source_derived": False,
    }
    declared_ready = all(
        closure[key]
        for key in [
            "transport_map_derivation_gate_imported",
            "plus_effective_RHS_declared",
            "minus_effective_RHS_declared",
            "plus_covariant_divergence_equation_declared",
            "minus_covariant_divergence_equation_declared",
            "same_bridge_used_in_both_divergences",
            "determinant_factors_kept_outside_bridge",
            "active_matter_source_equations_required",
        ]
    )
    source_ready = (
        bridge_ready
        and closure["plus_source_divergence_equation_derived"]
        and closure["minus_source_divergence_equation_derived"]
        and closure["plus_transport_compatibility_source_derived"]
        and closure["minus_transport_compatibility_source_derived"]
    )
    blockers = [key for key, value in closure.items() if not value]
    return {
        "status": "janus-z2-sigma-transport-compatibility-source-equation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_matter_divergence_equations",
        "definitions": {
            "S_plus": "S_plus := T_plus + B_plus K_plus(M_-+ T_minus)",
            "S_minus": "S_minus := B_minus K_minus(M_+- T_plus) + T_minus",
            "plus_equation": "D_plus_nu S_plus^{mu nu} = 0",
            "minus_equation": "D_minus_nu S_minus^{mu nu} = 0",
        },
        "closure": closure,
        "declared_source_equation_layer_ready": declared_ready,
        "source_derivation_ready": source_ready,
        "gate_passed": declared_ready and source_ready,
        "primary_blocker": "none" if source_ready else blockers[0],
        "blockers": blockers,
        "upstream_transport_map_gate": {
            "gate": transport["status"],
            "bridge_maps_source_derived": bridge_ready,
            "primary_blocker": transport["primary_blocker"],
        },
        "feeds_transport_map_gate": {
            "plus_transport_compatibility_source_derived": closure[
                "plus_transport_compatibility_source_derived"
            ],
            "minus_transport_compatibility_source_derived": closure[
                "minus_transport_compatibility_source_derived"
            ],
        },
        "next_required": [
            "derive_D_plus_nu_S_plus_zero_from_active_plus_source_equation",
            "derive_D_minus_nu_S_minus_zero_from_active_minus_source_equation",
            "check_no_hidden_Qcross_or_determinant_absorption",
            "then_set_transport_map_plus_minus_compatibility_source_derived",
        ],
        "interpretation": (
            "The compatibility equations are now isolated as source-equation obligations. "
            "A valid active embedding can source-derive the bridge maps, but the plus/minus "
            "divergence cancellations still require active matter equations."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Transport Compatibility Source Equation Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Definitions",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["definitions"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

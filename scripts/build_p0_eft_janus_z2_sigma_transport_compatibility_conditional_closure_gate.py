from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_bianchi_conditional_closure_theorem import (
    build_payload as build_bianchi_conditional_payload,
)
from scripts.build_bianchi_connection_force_cancellation_target import (
    build_payload as build_connection_force_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_transport_compatibility_source_equation_gate import (
    build_payload as build_source_equation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_same_sector_stress_conservation_gate import (
    build_payload as build_stress_conservation_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_transport_compatibility_conditional_closure_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_transport_compatibility_conditional_closure_gate.json"
)


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    source_gate = build_source_equation_payload(embedding_manifest_path=embedding_manifest_path)
    stress = build_stress_conservation_payload()
    conditional = build_bianchi_conditional_payload()
    force = build_connection_force_payload()
    closure = {
        "source_equation_gate_imported": True,
        "same_sector_stress_conservation_gate_imported": True,
        "conditional_bianchi_theorem_imported": conditional["conditional_closure_proved"],
        "connection_force_targets_imported": force["sufficient_conditions_written"],
        "bridge_maps_source_derived": source_gate["closure"]["bridge_maps_source_derived"],
        "same_sector_plus_stress_conserved": stress["closure"][
            "same_sector_plus_stress_conserved"
        ],
        "same_sector_minus_stress_conserved": stress["closure"][
            "same_sector_minus_stress_conserved"
        ],
        "transported_minus_continuity_derived": False,
        "transported_plus_continuity_derived": False,
        "minus_to_plus_connection_force_cancellation_derived": False,
        "plus_to_minus_connection_force_cancellation_derived": False,
        "same_bridge_for_stress_and_optics": True,
        "plus_transport_compatibility_source_derived": False,
        "minus_transport_compatibility_source_derived": False,
    }
    declared_ready = (
        closure["source_equation_gate_imported"]
        and closure["same_sector_stress_conservation_gate_imported"]
        and closure["conditional_bianchi_theorem_imported"]
        and closure["connection_force_targets_imported"]
        and closure["same_bridge_for_stress_and_optics"]
    )
    source_ready = all(closure.values())
    blockers = [key for key, value in closure.items() if not value]
    return {
        "status": "janus-z2-sigma-transport-compatibility-conditional-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "conditional_lorentz_dust_transport_bianchi_closure",
        "closure": closure,
        "declared_conditional_layer_ready": declared_ready,
        "source_derivation_ready": source_ready,
        "gate_passed": declared_ready and source_ready,
        "primary_blocker": "none" if source_ready else blockers[0],
        "blockers": blockers,
        "sufficient_conditions": {
            "positive": conditional["positive_chain"],
            "negative": conditional["negative_chain"],
            "continuity_targets": force["continuity_targets"],
            "force_targets": force["force_targets"],
        },
        "upstream_same_sector_stress_conservation_gate": {
            "gate": stress["status"],
            "primary_blocker": stress["primary_blocker"],
            "same_sector_plus_stress_conserved": closure[
                "same_sector_plus_stress_conserved"
            ],
            "same_sector_minus_stress_conserved": closure[
                "same_sector_minus_stress_conserved"
            ],
        },
        "feeds_source_equation_gate": {
            "plus_transport_compatibility_source_derived": closure[
                "plus_transport_compatibility_source_derived"
            ],
            "minus_transport_compatibility_source_derived": closure[
                "minus_transport_compatibility_source_derived"
            ],
        },
        "next_required": [
            "derive_same_sector_plus_stress_conservation",
            "derive_same_sector_minus_stress_conservation",
            "derive_transported_minus_continuity",
            "derive_transported_plus_continuity",
            "derive_minus_to_plus_connection_force_cancellation",
            "derive_plus_to_minus_connection_force_cancellation",
        ],
        "interpretation": (
            "The algebraic Bianchi implication is now connected to the active Z2/Sigma "
            "transport branch. It remains conditional: the continuity, same-sector "
            "conservation and connection-force equations are not source-derived yet."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Transport Compatibility Conditional Closure Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

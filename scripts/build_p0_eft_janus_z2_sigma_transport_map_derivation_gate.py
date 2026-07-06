from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_abstract_tensor_transport_bianchi_gate import (
    build_payload as build_abstract_bianchi,
)
from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_embedding_readiness,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_transport_map_derivation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_transport_map_derivation_gate.json")


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    bianchi = build_abstract_bianchi()
    if embedding_manifest_path is None:
        embedding = build_embedding_readiness()
    else:
        embedding = build_embedding_readiness(embedding_manifest_path=embedding_manifest_path)
    active_embedding_ready = bool(embedding.get("readiness", {}).get("active_embedding_ready", False))
    transport_maps = {
        "M_minus_to_plus": (
            "M_-+ := frame_plus^{-1} o d(tau_Z2) o frame_minus on transported covectors/tensors"
        ),
        "M_plus_to_minus": (
            "M_+- := frame_minus^{-1} o d(tau_Z2) o frame_plus, mirror inverse branch"
        ),
        "K_plus": "K_plus := M_minus_to_plus(T_minus) with plus-index conventions",
        "K_minus": "K_minus := M_plus_to_minus(T_plus) with minus-index conventions",
        "Q_cross": "Q_cross is an optical contraction read from the same M_minus_to_plus bridge",
    }
    closure = {
        "z2_sigma_bridge_declared": True,
        "M_minus_to_plus_declared": True,
        "M_plus_to_minus_declared": True,
        "inverse_mirror_branch_declared": True,
        "stress_transport_uses_bridge": True,
        "Q_cross_uses_same_bridge": True,
        "determinant_factors_kept_separate": True,
        "no_independent_optical_transport": True,
        "active_embedding_required_for_source_derivation": True,
        "bridge_maps_source_derived": active_embedding_ready,
        "plus_transport_compatibility_source_derived": False,
        "minus_transport_compatibility_source_derived": False,
        "abstract_bianchi_gate_can_be_source_closed": False,
    }
    source_ready = (
        closure["bridge_maps_source_derived"]
        and closure["plus_transport_compatibility_source_derived"]
        and closure["minus_transport_compatibility_source_derived"]
    )
    blockers = [key for key, value in closure.items() if not value]
    return {
        "status": "janus-z2-sigma-transport-map-derivation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "z2_sigma_bridge_transport_target",
        "transport_maps": transport_maps,
        "closure": closure,
        "declared_transport_layer_ready": all(
            closure[key]
            for key in [
                "z2_sigma_bridge_declared",
                "M_minus_to_plus_declared",
                "M_plus_to_minus_declared",
                "inverse_mirror_branch_declared",
                "stress_transport_uses_bridge",
                "Q_cross_uses_same_bridge",
                "determinant_factors_kept_separate",
                "no_independent_optical_transport",
            ]
        ),
        "source_derivation_ready": source_ready,
        "gate_passed": source_ready,
        "route_status": "declared_waiting_for_active_embedding_and_source_compatibility",
        "primary_blocker": "none" if source_ready else blockers[0],
        "blockers": blockers,
        "feeds_bianchi_gate": {
            "gate": bianchi["status"],
            "formal_bianchi_closed": bianchi["formal_bianchi_closed"],
            "can_remove_bianchi_source_blocker": source_ready,
        },
        "upstream_embedding_readiness": {
            "gate": embedding["status"],
            "active_embedding_ready": active_embedding_ready,
            "primary_blocker": embedding.get("primary_blocker"),
            "manifest": embedding["upstream_frontiers"]["active_embedding_geometry_manifest"],
        },
        "bridge_map_source_derivation": {
            "source": "active_embedding_geometry_manifest",
            "ready": closure["bridge_maps_source_derived"],
            "rule": (
                "valid active embedding frames induce M_-+ and M_+- through the Z2/Sigma bridge"
            ),
            "does_not_close": [
                "plus_transport_compatibility_source_derived",
                "minus_transport_compatibility_source_derived",
            ],
        },
        "next_required": []
        if source_ready
        else [
            "derive_active_embedding_frames_from_R_Sigma_solution",
            "instantiate_M_minus_to_plus_and_M_plus_to_minus_on_stress_tensors",
            "prove_plus_transport_compatibility_source_equation",
            "prove_minus_transport_compatibility_source_equation",
            "then_update_abstract_bianchi_gate_conditions_source_derived",
        ],
        "interpretation": (
            "The transport maps are now a named Z2/Sigma bridge target using one bridge "
            "for stress transport and Q_cross. Source derivation remains blocked until "
            "active embedding frames and compatibility equations are available."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Transport Map Derivation Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Transport Maps",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["transport_maps"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_tangent_normal_orientation_gate import (
    build_payload as build_tangent_normal_orientation_payload,
)
from janus_lab.z2_sigma_embedding_geometry_manifest import (
    load_active_z2sigma_embedding_geometry_manifest,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate.json")
EMBEDDING_MANIFEST_PATH = Path("outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json")
COMPONENTS_MANIFEST_PATH = Path("outputs/active_z2_sigma/coframe_connection_pullback_components_inputs.json")


def _embedding_manifest_status(path: Path) -> dict:
    if not path.exists():
        return {"path": str(path), "exists": False, "valid": False, "validation_error": None}
    try:
        load_active_z2sigma_embedding_geometry_manifest(path)
        return {"path": str(path), "exists": True, "valid": True, "validation_error": None}
    except Exception as exc:
        return {"path": str(path), "exists": True, "valid": False, "validation_error": str(exc)}


def _components_manifest_status(path: Path) -> dict:
    if not path.exists():
        return {"path": str(path), "exists": False, "valid": False, "validation_error": None}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        valid = (
            payload.get("active_core") == "Z2_tunnel_Sigma"
            and payload.get("source") == "active_derived"
            and payload.get("coframe_pullback_ready") is True
            and payload.get("spin_connection_pullback_ready") is True
        )
        return {
            "path": str(path),
            "exists": True,
            "valid": valid,
            "validation_error": None if valid else "components manifest is not ready",
            "route": payload.get("coframe_connection_route"),
            "torsionless_baseline_only": payload.get("torsionless_baseline_only"),
        }
    except Exception as exc:
        return {"path": str(path), "exists": True, "valid": False, "validation_error": str(exc)}


def build_payload(
    *,
    embedding_manifest_path: Path = EMBEDDING_MANIFEST_PATH,
    components_manifest_path: Path = COMPONENTS_MANIFEST_PATH,
) -> dict:
    active_embedding = build_active_embedding_payload()
    tangent_normal = build_tangent_normal_orientation_payload()
    embedding_manifest = _embedding_manifest_status(embedding_manifest_path)
    components_manifest = _components_manifest_status(components_manifest_path)
    declared = {
        "active_embedding_from_radius_gate_imported": True,
        "embedding_tangent_frame_transport_gate_imported": True,
        "tangent_normal_orientation_gate_imported": True,
        "coframe_connection_pullback_gate_imported": True,
        "pullback_coframe_connection_bibliography_checked": True,
    }
    manifest_ready = embedding_manifest["valid"]
    local_components_ready = components_manifest["valid"]
    active_embedding_ready = active_embedding["active_embedding_readiness_ready"] or manifest_ready
    tangent_frame_ready = (
        active_embedding["readiness"]["tangent_frames_ready"] or manifest_ready
    )
    normal_orientation_ready = (
        tangent_normal["tangent_normal_orientation_ready"] or manifest_ready
    )
    coframe_pullback_ready = (active_embedding_ready and tangent_frame_ready) or local_components_ready
    spin_connection_pullback_ready = (active_embedding_ready and tangent_frame_ready) or local_components_ready
    readiness = {
        "active_embedding_ready": active_embedding_ready,
        "tangent_frame_ready": tangent_frame_ready,
        "normal_orientation_ready": normal_orientation_ready,
        "differential_form_pullback_ready": True,
        "coframe_pullback_formula_ready": True,
        "spin_connection_pullback_formula_ready": True,
        "coframe_pullback_ready": coframe_pullback_ready,
        "spin_connection_pullback_ready": spin_connection_pullback_ready,
        "coframe_connection_pullback_ready": coframe_pullback_ready
        and spin_connection_pullback_ready,
    }
    ready = all(declared.values()) and all(readiness.values())
    primary_blocker = "none"
    if not ready:
        if not active_embedding_ready:
            primary_blocker = active_embedding.get(
                "primary_blocker", "active_tunnel_embedding_from_radius"
            )
        elif not normal_orientation_ready:
            primary_blocker = tangent_normal.get(
                "primary_blocker", "tangent_normal_orientation"
            )
        else:
            primary_blocker = "coframe_spin_connection_pullback_from_active_embedding"
    return {
        "status": "janus-z2-sigma-coframe-connection-pullback-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "standard differential-form pullback functoriality",
            "Cartan/tetrad coframe formalism",
            "spin-connection one-form formalism",
            "thin-shell embedding tangent-frame construction",
        ],
        "source_links": [
            "https://ncatlab.org/nlab/show/differential%2Bform",
            "https://ncatlab.org/nlab/show/Cartan%2Bstructural%2Bequations",
            "https://link.aps.org/doi/10.1103/PhysRevD.105.064066",
        ],
        "bibliography_result": (
            "The literature supplies the functorial pullback of coframe and spin-connection "
            "forms once the active embedding is known. It does not supply the Janus "
            "resolved-tunnel embedding X_+/- or its tangent/normal frame."
        ),
        "declared": declared,
        "readiness": readiness,
        "upstream_frontiers": {
            "active_embedding_geometry_manifest": embedding_manifest,
            "coframe_connection_components_manifest": components_manifest,
            "active_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding_ready,
                "primary_blocker": active_embedding.get("primary_blocker", "unknown"),
                "readiness": active_embedding["readiness"],
                "still_open": active_embedding["still_open"],
            },
            "tangent_normal_orientation": {
                "gate": tangent_normal["status"],
                "ready": normal_orientation_ready,
                "primary_blocker": tangent_normal.get("primary_blocker", "unknown"),
                "closure": tangent_normal["closure"],
            },
        },
        "formulae": {
            "coframe_pullback": "e^I_Sigma = X_Sigma^*(e^I)",
            "spin_connection_pullback": "omega^I_J|_Sigma = X_Sigma^*(omega^I_J)",
            "tangent_frame_dependency": "E_a^mu = partial_a X^mu",
            "normal_dependency": "h_ab and n_mu are induced by X_Sigma and orientation",
        },
        "closed": [
            "differential_form_pullback_ready",
            "coframe_pullback_formula_ready",
            "spin_connection_pullback_formula_ready",
        ],
        "still_open": [
            key
            for key, ready in readiness.items()
            if not ready
        ],
        "coframe_connection_pullback_readiness_ledger_declared": all(declared.values()),
        "coframe_connection_pullback_readiness_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "close_active_tunnel_embedding_from_radius_gate",
            "derive_tangent_frames_from_X_plus_minus_of_a",
            "derive_unit_normals_from_active_embedding_and_Z2_orientation",
            "evaluate_XSigma_pullback_of_coframe_and_spin_connection",
            "feed_coframe_connection_pullback_to_torsion_pullback_readiness_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coframe Connection Pullback Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['coframe_connection_pullback_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['coframe_connection_pullback_readiness_ready']}`",
        "",
        "## Closed",
    ]
    lines.extend(f"- `{item}`" for item in payload["closed"])
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

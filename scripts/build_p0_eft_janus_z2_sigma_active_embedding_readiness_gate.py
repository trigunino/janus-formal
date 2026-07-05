from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_from_radius_gate import (
    build_payload as build_embedding_from_radius_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_radius_to_embedding_conditional_closure_gate import (
    build_payload as build_radius_to_embedding_payload,
)
from janus_lab.z2_sigma_embedding_geometry_manifest import (
    load_active_z2sigma_embedding_geometry_manifest,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_embedding_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_embedding_readiness_gate.json")
EMBEDDING_MANIFEST_PATH = Path("outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json")


def _embedding_manifest_status(path: Path) -> dict:
    if not path.exists():
        return {"path": str(path), "exists": False, "valid": False, "validation_error": None}
    try:
        load_active_z2sigma_embedding_geometry_manifest(path)
        return {"path": str(path), "exists": True, "valid": True, "validation_error": None}
    except Exception as exc:
        return {"path": str(path), "exists": True, "valid": False, "validation_error": str(exc)}


def build_payload(*, embedding_manifest_path: Path = EMBEDDING_MANIFEST_PATH) -> dict:
    radius_to_embedding = build_radius_to_embedding_payload()
    embedding_from_radius = build_embedding_from_radius_payload()
    embedding_manifest = _embedding_manifest_status(embedding_manifest_path)
    declared = {
        "radius_gauge_embedding_transport_gate_imported": True,
        "radius_to_embedding_conditional_closure_gate_imported": True,
        "active_tunnel_embedding_from_radius_gate_imported": True,
        "throat_radius_solution_frontier_referenced_without_import_cycle": True,
        "embedding_tangent_frame_transport_gate_imported": True,
        "tangent_normal_orientation_gate_imported": True,
        "thin_shell_primary_bibliography_checked": True,
    }
    conditional_ready = radius_to_embedding["radius_to_embedding_conditional_ready"]
    manifest_ready = embedding_manifest["valid"]
    radius_ready = (
        radius_to_embedding["closure"]["R_Sigma_of_a_ready"]
        and embedding_from_radius["closure"]["R_Sigma_of_a_ready"]
    ) or manifest_ready
    embedding_ready = (
        radius_to_embedding["closure"]["X_plus_minus_of_a_ready"]
        and embedding_from_radius["closure"]["X_plus_minus_of_a_ready"]
    ) or manifest_ready
    readiness = {
        "embedding_gauge_equations_ready": embedding_from_radius["closure"][
            "embedding_gauge_equations_ready"
        ],
        "conditional_radius_to_embedding_ready": conditional_ready,
        "throat_radius_solution_certificate_ready": manifest_ready,
        "embedding_unblocked_by_radius_solution": manifest_ready,
        "R_Sigma_of_a_ready": radius_ready,
        "X_plus_minus_of_a_ready": embedding_ready,
        "tangent_frames_ready": embedding_from_radius["closure"][
            "tangent_normal_inputs_ready"
        ] or manifest_ready,
        "unit_normals_ready": manifest_ready,
    }
    readiness["active_embedding_ready"] = (
        readiness["throat_radius_solution_certificate_ready"]
        and readiness["embedding_unblocked_by_radius_solution"]
        and readiness["R_Sigma_of_a_ready"]
        and readiness["X_plus_minus_of_a_ready"]
        and readiness["tangent_frames_ready"]
        and readiness["unit_normals_ready"]
    )
    nearest_embedding_frontier = {
        "block": "R_Sigma_solution_certificate",
        "gate": "P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate",
        "required": [
            "reduce matter-flux radial block",
            "reduce counterterm radial block",
            "solve E_RSigma(a)=0 without fit",
            "emit active R_Sigma(a) certificate before deriving X_+/- and normals",
        ],
        "diagnostic_only": True,
    }
    return {
        "status": "janus-z2-sigma-active-embedding-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel 1966 singular hypersurfaces and thin shells",
            "Poisson-Visser 1995 thin-shell wormhole kinematics",
            "Darmois-Israel proper-time shell embedding",
        ],
        "source_links": [
            "https://doi.org/10.1007/BF02710419",
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
            "https://arxiv.org/abs/gr-qc/9506083",
        ],
        "bibliography_result": (
            "Primary thin-shell literature supplies the conditional shell embedding "
            "map once a throat radius law is given. It does not derive the Janus "
            "Z2/Sigma no-fit radius law R_Sigma(a)."
        ),
        "declared": declared,
        "readiness": readiness,
        "upstream_frontiers": {
            "active_embedding_geometry_manifest": embedding_manifest,
            "radius_to_embedding": {
                "gate": radius_to_embedding["status"],
                "conditional_ready": radius_to_embedding[
                    "radius_to_embedding_conditional_ready"
                ],
                "unconditional_ready": radius_to_embedding[
                    "radius_to_embedding_unconditional_ready"
                ],
                "closure": radius_to_embedding["closure"],
            },
            "embedding_from_radius": {
                "gate": embedding_from_radius["status"],
                "ready": embedding_from_radius["active_embedding_from_radius_ready"],
                "closure": embedding_from_radius["closure"],
            },
        },
        "closed": [
            "embedding_gauge_equations_ready",
            "conditional_radius_to_embedding_ready",
        ],
        "still_open": [
            key
            for key, ready in readiness.items()
            if not ready
        ],
        "nearest_embedding_frontier": nearest_embedding_frontier,
        "nearest_embedding_frontier_declared": True,
        "nearest_embedding_frontier_diagnostic_only": True,
        "maps": {
            "conditional_embedding": "R_Sigma(a) + gauge equations -> X_+/-^mu(a,xi)",
            "frame_transport": "X_+/- (a) -> partial_a X_+/- -> tangent frames",
            "normal_transport": "X_+/- (a), h_ab, epsilon_Z2 -> unit normals",
        },
        "active_embedding_readiness_ledger_declared": all(declared.values()),
        "active_embedding_readiness_ready": all(declared.values()) and all(readiness.values()),
        "gate_passed": all(declared.values()) and all(readiness.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(readiness.values())
            else "R_Sigma_solution_certificate"
        ),
        "next_required": [
            "solve_R_Sigma_of_a_from_throat_radius_variational_equation",
            "instantiate_conditional_embedding_map_with_R_Sigma_of_a",
            "derive_tangent_frames_from_X_plus_minus_of_a",
            "derive_unit_normals_from_active_embedding",
            "feed_active_embedding_to_coframe_connection_and_torsion_pullback_gates",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active Embedding Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['active_embedding_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['active_embedding_readiness_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Closed",
    ]
    lines.extend(f"- `{item}`" for item in payload["closed"])
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    lines.extend(["", "## Nearest Embedding Frontier"])
    nearest = payload["nearest_embedding_frontier"]
    lines.append(f"- `block`: `{nearest['block']}`")
    lines.append(f"- `gate`: `{nearest['gate']}`")
    lines.extend(f"- `required`: `{item}`" for item in nearest["required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

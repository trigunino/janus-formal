from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_embedding_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_embedding_readiness_gate.json")


def build_payload() -> dict:
    declared = {
        "radius_gauge_embedding_transport_gate_imported": True,
        "radius_to_embedding_conditional_closure_gate_imported": True,
        "active_tunnel_embedding_from_radius_gate_imported": True,
        "embedding_tangent_frame_transport_gate_imported": True,
        "tangent_normal_orientation_gate_imported": True,
        "thin_shell_primary_bibliography_checked": True,
    }
    readiness = {
        "embedding_gauge_equations_ready": True,
        "conditional_radius_to_embedding_ready": True,
        "R_Sigma_of_a_ready": False,
        "X_plus_minus_of_a_ready": False,
        "tangent_frames_ready": False,
        "unit_normals_ready": False,
        "active_embedding_ready": False,
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
        "closed": [
            "embedding_gauge_equations_ready",
            "conditional_radius_to_embedding_ready",
        ],
        "still_open": [
            "R_Sigma_of_a_ready",
            "X_plus_minus_of_a_ready",
            "tangent_frames_ready",
            "unit_normals_ready",
            "active_embedding_ready",
        ],
        "maps": {
            "conditional_embedding": "R_Sigma(a) + gauge equations -> X_+/-^mu(a,xi)",
            "frame_transport": "X_+/- (a) -> partial_a X_+/- -> tangent frames",
            "normal_transport": "X_+/- (a), h_ab, epsilon_Z2 -> unit normals",
        },
        "active_embedding_readiness_ledger_declared": all(declared.values()),
        "active_embedding_readiness_ready": all(declared.values()) and all(readiness.values()),
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

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_from_radius_gate import (
    build_payload as build_active_tunnel_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_embedding_regularity_equivariance_gate import (
    build_payload as build_embedding_regularity_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_smooth_embedded_throat_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_smooth_embedded_throat_gate.json")


def build_payload() -> dict:
    active_embedding = build_active_tunnel_embedding_payload()
    embedding_regularity = build_embedding_regularity_payload()
    declared = {
        "embedded_submanifold_bibliography_checked": True,
        "tubular_neighborhood_prerequisite_checked": True,
        "active_tunnel_embedding_gate_declared": True,
        "embedding_regularity_equivariance_gate_declared": True,
        "sigma_throat_declared": True,
        "X_plus_minus_embedding_declared": True,
        "regular_radius_condition_declared": True,
        "Z2_equivariance_declared": True,
        "immersion_rank_condition_declared": True,
        "topological_embedding_condition_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "active_tunnel_embedding_ready": active_embedding["active_embedding_from_radius_ready"],
        "regular_throat_radius_derived": embedding_regularity["closure"]["regular_throat_radius_derived"],
        "immersion_rank_derived": embedding_regularity["closure"]["immersion_rank_derived"],
        "topological_embedding_derived": embedding_regularity["closure"]["topological_embedding_derived"],
        "Z2_equivariant_embedding_derived": embedding_regularity["closure"]["Z2_equivariant_embedding_derived"],
        "sigma_smooth_embedded_throat_derived": False,
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = (
        "none"
        if ready
        else active_embedding.get("primary_blocker")
        or embedding_regularity.get("primary_blocker")
        or "active_tunnel_embedding_from_RSigma"
    )
    return {
        "status": "janus-z2-sigma-smooth-embedded-throat-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "embedded submanifold definition in smooth manifold theory",
            "tubular neighborhood theorem prerequisites",
            "Janus active tunnel embedding gate",
            "active embedding regularity/equivariance gate",
        ],
        "source_links": [
            "https://ncatlab.org/nlab/show/tubular%2Bneighborhood%2Btheorem",
            "https://math.mit.edu/~hrm/palestine/lee-smooth-manifolds.pdf",
            "https://msp.org/agt/2007/7-1/agt-v7-n1-p01-p.pdf",
        ],
        "bibliography_result": (
            "Smooth manifold references reduce the collar/tubular step to proving "
            "that Sigma is a smooth embedded submanifold/throat. The active Janus "
            "proof still needs X_+/- embeddings, regular nonzero throat radius, "
            "immersion rank, topological embedding, and Z2 equivariance."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "active_tunnel_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding["active_embedding_from_radius_ready"],
                "closure": active_embedding["closure"],
                "primary_blocker": active_embedding.get("primary_blocker"),
            },
            "embedding_regularity_equivariance": {
                "gate": embedding_regularity["status"],
                "ready": embedding_regularity["embedding_regularity_equivariance_ready"],
                "closure": embedding_regularity["closure"],
                "primary_blocker": embedding_regularity.get("primary_blocker"),
            },
        },
        "formulas": {
            "embedding": "X_pm(a, xi): Sigma -> M_pm",
            "rank": "rank(dX_pm)=dim(Sigma)",
            "regular_radius": "R_Sigma(a) > 0 on the resolved tunnel",
            "z2_equivariance": "tau o X_+(a,xi) = X_-(a,xi)",
        },
        "sigma_smooth_embedded_throat_ledger_declared": all(declared.values()),
        "sigma_smooth_embedded_throat_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "pass_embedding_regularity_equivariance_gate",
            "pass_active_tunnel_embedding_of_a_gate",
            "derive_regular_throat_radius_RSigma_of_a",
            "prove_embedding_immersion_rank",
            "prove_embedding_is_topological_embedding",
            "prove_Z2_equivariance_of_embedding",
            "feed_result_to_collar_tubular_neighborhood_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Smooth Embedded Throat Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['sigma_smooth_embedded_throat_ledger_declared']}`",
        f"Ready: `{payload['sigma_smooth_embedded_throat_ready']}`",
        "",
        "## Bibliography",
        payload["bibliography_result"],
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

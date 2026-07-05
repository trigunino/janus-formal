from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_embedding_regularity_equivariance_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_embedding_regularity_equivariance_gate.json")


def build_payload() -> dict:
    declared = {
        "embedding_bibliography_checked": True,
        "equivariant_tubular_bibliography_checked": True,
        "active_tunnel_embedding_gate_declared": True,
        "X_plus_minus_maps_declared": True,
        "regular_radius_condition_declared": True,
        "immersion_rank_test_declared": True,
        "injectivity_or_topological_embedding_test_declared": True,
        "Z2_equivariance_test_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "X_plus_minus_of_a_derived": False,
        "regular_throat_radius_derived": False,
        "immersion_rank_derived": False,
        "topological_embedding_derived": False,
        "Z2_equivariant_embedding_derived": False,
        "embedding_regularity_equivariance_ready": False,
    }
    return {
        "status": "janus-z2-sigma-embedding-regularity-equivariance-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "smooth embedding = immersion plus topological embedding",
            "constant-rank/immersion criterion",
            "equivariant collaring/tubular-neighborhood literature",
            "active tunnel embedding of a gate",
        ],
        "source_links": [
            "https://math.mit.edu/~hrm/palestine/lee-smooth-manifolds.pdf",
            "https://idv.sinica.edu.tw/ftliang/diff_geom/%2Adiff_geometry%28I%29/10.16/submfd.pdf",
            "https://ncatlab.org/nlab/show/equivariant%2Btubular%2Bneighbourhood",
            "https://msp.org/agt/2007/7-1/agt-v7-n1-p01-p.pdf",
        ],
        "bibliography_result": (
            "The standard criterion is not a new Janus law: X_pm must be an "
            "immersion of full Sigma rank and a topological embedding onto its "
            "image. For the Z2 tunnel, the embedding must also satisfy the deck "
            "equivariance condition before equivariant collars/tubes can be used."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "rank_test": "rank(dX_pm)=dim(Sigma)",
            "topological_embedding": "X_pm: Sigma -> X_pm(Sigma) is a homeomorphism",
            "z2_equivariance": "tau o X_+(a,xi)=X_-(a,xi)",
            "regularity": "R_Sigma(a)>0 and finite",
        },
        "embedding_regularity_equivariance_ledger_declared": all(declared.values()),
        "embedding_regularity_equivariance_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "active_tunnel_embedding_from_RSigma"
        ),
        "next_required": [
            "pass_active_tunnel_embedding_of_a_gate",
            "derive_X_plus_minus_of_a",
            "derive_regular_throat_radius_RSigma_of_a",
            "prove_rank_dX_equals_dim_Sigma",
            "prove_X_pm_are_topological_embeddings",
            "prove_Z2_equivariance_of_X_pm",
            "feed_result_to_sigma_smooth_embedded_throat_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Embedding Regularity Equivariance Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['embedding_regularity_equivariance_ledger_declared']}`",
        f"Ready: `{payload['embedding_regularity_equivariance_ready']}`",
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

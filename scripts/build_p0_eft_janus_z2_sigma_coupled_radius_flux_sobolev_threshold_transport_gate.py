from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_threshold_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_threshold_transport_gate.json")


def build_payload() -> dict:
    declared = {
        "sobolev_index_gate_imported": True,
        "gagliardo_trace_theorem_available": True,
        "sobolev_algebra_theorem_available": True,
        "sigma_dimension_three_used": True,
        "trace_loss_one_half_used": True,
        "candidate_bulk_index_at_least_three": True,
        "candidate_boundary_index_at_least_five_halves": True,
        "boundary_index_above_three_halves": True,
        "no_regularity_fit_to_observations": True,
    }
    transported = {
        "candidate_indices_pass_trace_threshold": True,
        "candidate_indices_pass_product_threshold": True,
        "normal_and_tangent_frame_support_still_open": True,
    }
    return {
        "status": "janus-z2-sigma-coupled-radius-flux-sobolev-threshold-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Gagliardo trace theorem for Sobolev traces on Lipschitz/smooth boundaries",
            "Sobolev multiplication theorem / algebra threshold s > n/2",
            "Boundary product regularity for thin-shell flux terms",
        ],
        "source_links": [
            "https://numdam.org/articles/10.5802/ambp.232/",
            "https://arxiv.org/abs/1512.07379",
            "https://link.springer.com/article/10.1007/BF02710419",
        ],
        "bibliography_result": (
            "The standard trace theorem transports H^s bulk regularity to a boundary "
            "trace with one-half derivative loss. The standard Sobolev algebra route "
            "controls products on 3D Sigma once s_Sigma > 3/2. The candidate "
            "s_bulk >= 3 gives s_Sigma >= 5/2, so trace and product thresholds are "
            "transported; normal/tangent frame support remains a separate geometry proof."
        ),
        "declared": declared,
        "transported": transported,
        "threshold_transport_ledger_declared": all(declared.values()),
        "trace_and_product_thresholds_transported": all(declared.values()) and all(transported.values()),
        "closed_from_sobolev_theorems": [
            "candidate_indices_pass_trace_threshold",
            "candidate_indices_pass_product_threshold",
        ],
        "still_open": [
            "candidate_indices_support_normal_and_tangent_traces",
            "normal_trace_continuity_for_n_mu[R_Sigma]",
            "tangent_frame_trace_continuity_for_e_a^mu[R_Sigma]",
        ],
        "next_required": [
            "prove_normal_trace_continuity_for_RSigma_regular_embeddings",
            "prove_tangent_frame_trace_continuity_for_RSigma_regular_embeddings",
            "feed_normal_tangent_support_to_sobolev_index_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coupled Radius-Flux Sobolev Threshold Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['threshold_transport_ledger_declared']}`",
        f"Trace/product thresholds transported: `{payload['trace_and_product_thresholds_transported']}`",
        "",
        "## Closed From Standard Theorems",
    ]
    lines.extend(f"- `{item}`" for item in payload["closed_from_sobolev_theorems"])
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

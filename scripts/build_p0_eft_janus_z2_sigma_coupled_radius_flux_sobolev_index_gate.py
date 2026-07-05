from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_index_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_index_gate.json")


def build_payload() -> dict:
    declared = {
        "trace_regularity_gate_imported": True,
        "gagliardo_trace_bibliography_checked": True,
        "sobolev_multiplication_bibliography_checked": True,
        "sigma_dimension_declared": True,
        "bulk_to_boundary_trace_loss_declared": True,
        "boundary_algebra_threshold_declared": True,
        "candidate_bulk_index_declared": True,
        "candidate_boundary_index_declared": True,
        "R_Sigma_regularity_index_declared": True,
        "T_pm_trace_regularity_index_declared": True,
        "no_index_fit_to_observations": True,
    }
    index_choice = {
        "bulk_dimension": 4,
        "sigma_dimension": 3,
        "trace_loss": "1/2 derivative for H^s bulk-to-boundary trace",
        "boundary_algebra_threshold": "s_Sigma > dim(Sigma)/2 = 3/2",
        "candidate_bulk_index": "s_bulk >= 3",
        "candidate_boundary_index": "s_Sigma = s_bulk - 1/2 >= 5/2",
        "R_Sigma_regularity": "H^3 plus C^2 representative where classical geometry is used",
        "T_pm_trace_regularity": "H^(5/2)(Sigma) or compatible algebra trace class",
    }
    obligations = {
        "candidate_indices_pass_trace_threshold": True,
        "candidate_indices_pass_product_threshold": True,
        "candidate_indices_support_normal_and_tangent_traces": False,
        "sobolev_index_choice_ready_for_trace_proof": False,
    }
    return {
        "status": "janus-z2-sigma-coupled-radius-flux-sobolev-index-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Gagliardo trace theorem lineage for Sobolev traces",
            "Sobolev multiplication theorem / algebra threshold",
            "Thin-shell flux requires boundary product T_pm e_a^mu n_mu",
        ],
        "source_links": [
            "https://numdam.org/articles/10.5802/ambp.232/",
            "https://arxiv.org/abs/1512.07379",
            "https://link.springer.com/article/10.1007/BF02710419",
        ],
        "bibliography_result": (
            "The standard trace/multiplication route suggests choosing a boundary trace "
            "regularity above dim(Sigma)/2 so products are controlled. For a 3D Sigma, "
            "a conservative ledger choice is s_bulk >= 3, giving s_Sigma >= 5/2."
        ),
        "declared": declared,
        "index_choice": index_choice,
        "obligations": obligations,
        "sobolev_index_ledger_declared": all(declared.values()),
        "sobolev_index_ready": all(declared.values()) and all(obligations.values()),
        "closed_from_standard_sobolev_theorems": [
            "candidate_indices_pass_trace_threshold",
            "candidate_indices_pass_product_threshold",
        ],
        "current_frontier": [
            "candidate_indices_support_normal_and_tangent_traces = false",
            "sobolev_index_choice_ready_for_trace_proof = false",
        ],
        "next_required": [
            "prove_s_bulk_ge_3_gives_boundary_trace_H_ge_5_over_2",
            "prove_H_5_over_2_on_3D_Sigma_is_product_algebra",
            "prove_normal_and_tangent_frame_traces_are_supported",
            "feed_index_choice_to_trace_regularity_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coupled Radius-Flux Sobolev Index Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['sobolev_index_ledger_declared']}`",
        f"Sobolev index ready: `{payload['sobolev_index_ready']}`",
        "",
        "## Candidate Indices",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["index_choice"].items())
    lines.extend(["", "## Closed From Standard Sobolev Theorems"])
    lines.extend(f"- `{item}`" for item in payload["closed_from_standard_sobolev_theorems"])
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_embedding_frame_trace_transport_gate import (
    build_payload as build_embedding_frame_trace_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_threshold_transport_gate import (
    build_payload as build_sobolev_threshold_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_trace_regularity_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_trace_regularity_gate.json")


def build_payload() -> dict:
    sobolev = build_sobolev_threshold_payload()
    frame = build_embedding_frame_trace_payload()
    declared = {
        "function_space_gate_imported": True,
        "sobolev_threshold_transport_imported": True,
        "embedding_frame_trace_transport_imported": True,
        "sobolev_trace_bibliography_checked": True,
        "embedding_trace_map_declared": True,
        "normal_trace_map_declared": True,
        "tangent_frame_trace_map_declared": True,
        "stress_trace_compatibility_declared": True,
        "product_space_declared": True,
        "no_pointwise_product_shortcut": True,
        "no_observational_trace_fit": True,
    }
    analytic_obligations = {
        "sobolev_trace_threshold_passed": sobolev["transported"][
            "candidate_indices_pass_trace_threshold"
        ],
        "sobolev_product_threshold_passed": sobolev["transported"][
            "candidate_indices_pass_product_threshold"
        ],
        "embedding_trace_continuous": frame["transported"][
            "tangent_frame_trace_continuous"
        ],
        "normal_trace_continuous": frame["transported"]["normal_trace_continuous"],
        "tangent_frame_trace_continuous": frame["transported"][
            "tangent_frame_trace_continuous"
        ],
        "stress_normal_product_well_defined": (
            sobolev["transported"]["candidate_indices_pass_product_threshold"]
            and frame["transported"]["candidate_indices_support_normal_and_tangent_traces"]
        ),
        "flux_functional_trace_ready": frame["partial_subchannels"][
            "active_trace_transport"
        ]["ready"],
    }
    return {
        "status": "janus-z2-sigma-coupled-radius-flux-trace-regularity-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Sobolev trace theorem for boundary restrictions",
            "Thin-shell stress/flux conservation template",
            "Boundary product regularity needed for T_pm e_a^mu n_mu",
        ],
        "source_links": [
            "https://books.google.com/books?id=b3frCAAAQBAJ",
            "https://link.springer.com/article/10.1007/BF02710419",
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
        ],
        "bibliography_result": (
            "Trace theorems support boundary restrictions only after explicit regularity "
            "choices. The Janus Z2/Sigma flux functional still needs continuity of the "
            "embedding, normal, tangent-frame, and stress traces in compatible spaces."
        ),
        "declared": declared,
        "analytic_obligations": analytic_obligations,
        "upstream_frontiers": {
            "sobolev_threshold_transport": {
                "gate": sobolev["status"],
                "ready": sobolev["trace_and_product_thresholds_transported"],
                "still_open": sobolev["still_open"],
            },
            "embedding_frame_trace_transport": {
                "gate": frame["status"],
                "ready": frame["embedding_frame_trace_transport_ready"],
                "conditional_formulae_ready": frame["conditional_formulae_ready"],
                "current_frontier": frame["current_frontier"],
            },
        },
        "closed_from_standard_theorems": [
            key
            for key in [
                "sobolev_trace_threshold_passed",
                "sobolev_product_threshold_passed",
            ]
            if analytic_obligations[key]
        ],
        "trace_maps": [
            "R_Sigma -> X_+/-[R_Sigma]|_Sigma",
            "R_Sigma -> n_mu[R_Sigma]|_Sigma",
            "R_Sigma -> e_a^mu[R_Sigma]|_Sigma",
            "T_pm -> T_pm|_Sigma in a compatible trace/product space",
        ],
        "trace_regularity_ledger_declared": all(declared.values()),
        "trace_regularity_ready": all(declared.values()) and all(analytic_obligations.values()),
        "current_frontier": [
            "embedding_trace_continuous = false",
            "normal_trace_continuous = false",
            "tangent_frame_trace_continuous = false",
            "stress_normal_product_well_defined = false",
            "flux_functional_trace_ready = false",
        ],
        "next_required": [
            "choose_minimal_Sobolev_or_Ck_indices_for_RSigma_and_Tpm",
            "prove_embedding_normal_tangent_trace_continuity",
            "prove_Tpm_e_n_product_well_defined",
            "feed_flux_functional_trace_ready_to_function_space_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coupled Radius-Flux Trace Regularity Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['trace_regularity_ledger_declared']}`",
        f"Trace regularity ready: `{payload['trace_regularity_ready']}`",
        "",
        "## Trace Maps",
    ]
    lines.extend(f"- `{item}`" for item in payload["trace_maps"])
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

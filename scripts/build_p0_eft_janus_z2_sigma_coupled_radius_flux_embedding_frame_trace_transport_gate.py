from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flux_projection_domain_gate import (
    build_payload as build_flux_projection_domain_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_embedding_frame_trace_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_embedding_frame_trace_transport_gate.json")


def build_payload() -> dict:
    domain = build_flux_projection_domain_payload()
    declared = {
        "normal_tangent_trace_support_gate_imported": True,
        "embedding_regularity_equivariance_imported": True,
        "hypersurface_frame_theorem_imported": True,
        "frame_trace_transport_declared": True,
        "no_independent_frame_fit": True,
    }
    prerequisites = {
        "regular_embedding_ready": domain["closure"]["regular_embedding_ready"],
        "coorientation_ready": domain["closure"]["coorientation_ready"],
        "induced_metric_nondegenerate_ready": domain["closure"][
            "induced_metric_nondegenerate_ready"
        ],
    }
    conditional_formulae_ready = {
        "tangent_frame_formula_ready": True,
        "normal_covector_formula_ready": True,
        "induced_metric_pullback_formula_ready": True,
    }
    transported = {
        "tangent_frame_trace_supported": False,
        "normal_trace_supported": False,
        "tangent_frame_trace_continuous": False,
        "normal_trace_continuous": False,
        "candidate_indices_support_normal_and_tangent_traces": False,
    }
    return {
        "status": "janus-z2-sigma-coupled-radius-flux-embedding-frame-trace-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "regular hypersurface: tangent frame from embedding differential",
            "co-oriented nondegenerate hypersurface: unit normal from embedding and metric",
            "trace/product thresholds already transported by Sobolev gate",
        ],
        "source_links": [
            "https://math.mit.edu/~hrm/palestine/lee-smooth-manifolds.pdf",
            "https://projecteuclid.org/journals/journal-of-differential-geometry/volume-66/issue-1/On-the-Sobolev-Space-of-Isometric-Immersions/10.4310/jdg/1090415029.pdf",
            "https://numdam.org/articles/10.5802/ambp.232/",
        ],
        "bibliography_result": (
            "The tangent frame and unit normal are not independent Janus data. They are "
            "transported from a regular co-oriented embedding with nondegenerate induced "
            "metric. Since the active embedding gate is still open, this transport is "
            "recorded as conditional and does not close the flux trace gate yet."
        ),
        "declared": declared,
        "prerequisites": prerequisites,
        "conditional_formulae_ready": conditional_formulae_ready,
        "upstream_frontiers": {
            "flux_projection_domain": {
                "gate": domain["status"],
                "ready": domain["flux_projection_domain_ready"],
                "primary_blocker": domain["primary_blocker"],
                "closure": domain["closure"],
            },
        },
        "transported": transported,
        "formulae": {
            "tangent_frame": "e_a^mu = partial_a X^mu",
            "induced_metric": "h_ab = g_munu e_a^mu e_b^nu",
            "unit_normal": "n_mu = eps_Z2 partial_mu Phi / sqrt(|g^alpha_beta partial_alpha Phi partial_beta Phi|)",
        },
        "partial_subchannels": {
            "frame_normal_formulae": {
                "ready": all(conditional_formulae_ready.values()),
                "status": "formula_only_not_active_trace_transport_ready",
            },
            "active_trace_transport": {
                "ready": all(prerequisites.values()) and all(transported.values()),
                "status": "blocked_on_regular_embedding_and_nondegenerate_induced_metric",
            },
        },
        "conditional_transport_rule": (
            "regular_embedding_ready and coorientation_ready and induced_metric_nondegenerate_ready "
            "=> tangent/normal trace support and continuity"
        ),
        "embedding_frame_trace_transport_ledger_declared": all(declared.values()),
        "embedding_frame_trace_transport_ready": all(declared.values())
        and all(prerequisites.values())
        and all(conditional_formulae_ready.values())
        and all(transported.values()),
        "primary_blocker": domain["primary_blocker"],
        "current_frontier": [
            *[
                f"{key} = false"
                for key, ready in prerequisites.items()
                if not ready
            ],
            *[
                f"{key} = false"
                for key, ready in transported.items()
                if not ready
            ],
        ],
        "next_required": [
            "close_embedding_regularity_equivariance_gate",
            "derive_coorientation_from_Z2_Sigma_tunnel_orientation",
            "prove_induced_metric_nondegeneracy_on_Sigma",
            "then_transport_tangent_normal_trace_continuity",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coupled Radius-Flux Embedding Frame Trace Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['embedding_frame_trace_transport_ledger_declared']}`",
        f"Transport ready: `{payload['embedding_frame_trace_transport_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Conditional Transport Rule",
        f"`{payload['conditional_transport_rule']}`",
        "",
        "## Formulae",
        *[f"- `{key}`: `{value}`" for key, value in payload["formulae"].items()],
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

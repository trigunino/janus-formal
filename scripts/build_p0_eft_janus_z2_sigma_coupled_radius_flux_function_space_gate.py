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


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_function_space_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coupled_radius_flux_function_space_gate.json")


def build_payload() -> dict:
    sobolev = build_sobolev_threshold_payload()
    frame = build_embedding_frame_trace_payload()
    declared = {
        "well_posedness_gate_imported": True,
        "thin_shell_regularity_bibliography_checked": True,
        "R_Sigma_domain_declared": True,
        "flux_domain_declared": True,
        "embedding_trace_domain_declared": True,
        "boundary_data_space_declared": True,
        "gauge_slice_declared": True,
        "equation_map_domain_codomain_declared": True,
        "no_distributional_product_ambiguity_declared": True,
        "no_observational_norm_fit": True,
        "sobolev_threshold_transport_imported": True,
        "embedding_frame_trace_transport_imported": True,
    }
    analytic_obligations = {
        "trace_threshold_passed": sobolev["transported"][
            "candidate_indices_pass_trace_threshold"
        ],
        "product_threshold_passed": sobolev["transported"][
            "candidate_indices_pass_product_threshold"
        ],
        "embedding_trace_map_continuous": frame["transported"][
            "tangent_frame_trace_continuous"
        ],
        "normal_trace_map_continuous": frame["transported"]["normal_trace_continuous"],
        "flux_functional_well_defined": frame["transported"][
            "candidate_indices_support_normal_and_tangent_traces"
        ],
        "equation_map_continuous": False,
        "linearized_map_fredholm_or_invertible": False,
        "function_space_ready_for_well_posedness": False,
    }
    ready = all(declared.values()) and all(analytic_obligations.values())
    primary_blocker = (
        "none"
        if ready
        else frame.get("primary_blocker")
        or "embedding_frame_trace_transport"
    )
    return {
        "status": "janus-z2-sigma-coupled-radius-flux-function-space-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell junction/conservation regularity template",
            "Poisson-Visser throat dynamics regularity template",
            "Sobolev/trace-map regularity needed for boundary flux products",
        ],
        "source_links": [
            "https://link.springer.com/article/10.1007/BF02710419",
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
            "https://books.google.com/books?id=b3frCAAAQBAJ",
        ],
        "bibliography_result": (
            "Thin-shell literature fixes the geometric conservation template. The Janus "
            "Z2/Sigma coupled radius-flux system still needs explicit function spaces "
            "so products like T_pm e_a^mu n_mu and traces X_pm[R_Sigma] are well-defined."
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
                "current_frontier": frame["current_frontier"],
                "primary_blocker": frame.get("primary_blocker"),
            },
        },
        "candidate_spaces": {
            "R_Sigma": "C^2 or Sobolev H^s radial function with s high enough for traces",
            "F_a_Z2Sigma": "boundary one-form/function in the matching trace space",
            "X_pm_trace": "embedding trace map controlled by R_Sigma regularity",
            "gauge_slice": "homogeneous throat-radius/embedding mode fixed before uniqueness",
        },
        "function_space_ledger_declared": all(declared.values()),
        "function_space_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, ready in analytic_obligations.items()
            if not ready
        ],
        "next_required": [
            "prove_trace_regularities_for_X_pm_of_RSigma",
            "prove_flux_functional_well_defined_on_declared_spaces",
            "prove_equation_map_continuity",
            "prove_linearized_operator_invertibility_or_Fredholm_alternative",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coupled Radius-Flux Function Space Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['function_space_ledger_declared']}`",
        f"Function space ready: `{payload['function_space_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
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

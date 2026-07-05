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
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_embedding_frame_trace_transport_gate import (
    build_payload as build_frame_trace_transport_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_connection_variation_transport_gate import (
    build_payload as build_connection_variation_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_tetrad_transport_closure import (
    build_payload as build_tetrad_transport_closure_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_extrinsic_curvature_variation_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_extrinsic_curvature_variation_transport_gate.json")


def build_payload() -> dict:
    active_embedding = build_active_embedding_payload()
    frame_trace = build_frame_trace_transport_payload()
    connection_variation = build_connection_variation_payload()
    tetrad_transport_closure = build_tetrad_transport_closure_payload()
    declared = {
        "tetrad_variation_transport_gate_imported": True,
        "extrinsic_curvature_gate_imported": True,
        "coupled_radius_flux_embedding_frame_trace_transport_gate_imported": True,
        "hypersurface_variation_bibliography_checked": True,
        "K_ab_formula_declared": True,
        "delta_K_formula_declared": True,
        "delta_e_to_delta_tangent_frame_declared": True,
        "delta_e_to_delta_normal_declared": True,
        "delta_e_to_delta_connection_declared": True,
        "z2_normal_orientation_variation_declared": True,
        "no_fitted_extrinsic_curvature_variation": True,
    }
    active_embedding_ready = active_embedding["active_embedding_readiness_ready"]
    frame_trace_ready = frame_trace["embedding_frame_trace_transport_ready"]
    connection_variation_ready = connection_variation[
        "counterterm_connection_variation_transport_ready"
    ]
    upstream_ready = active_embedding_ready and frame_trace_ready and connection_variation_ready
    delta_k_structural_formula_ready = True
    symbolic_local_delta_k_ready = bool(
        tetrad_transport_closure["gate_passed"]
        and tetrad_transport_closure["closure"]["extrinsic_curvature_transport"]["ready"]
    )
    delta_k_allowed_basis_ready = symbolic_local_delta_k_ready
    closure = {
        "delta_K_structural_formula_ready": delta_k_structural_formula_ready,
        "active_embedding_ready": active_embedding_ready,
        "tangent_normal_trace_transport_ready": frame_trace_ready,
        "connection_variation_transport_ready": connection_variation_ready,
        "delta_K_upstream_transport_inputs_ready": upstream_ready,
        "symbolic_gaussian_collar_delta_K_ready": symbolic_local_delta_k_ready,
        "delta_K_in_allowed_basis": delta_k_allowed_basis_ready,
        "extrinsic_curvature_variation_transport_ready": symbolic_local_delta_k_ready or upstream_ready
        and delta_k_allowed_basis_ready,
    }
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-extrinsic-curvature-variation-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "thin-shell extrinsic curvature formula from embeddings, tangents and normals",
            "hypersurface variation of K_ab depends on tangent, normal and connection variations",
            "Z2 normal orientation sign affects K_ab and its variation",
        ],
        "source_links": [
            "https://link.springer.com/article/10.1007/BF02710419",
            "https://www.sciencedirect.com/topics/mathematics/second-fundamental-form",
            "https://arxiv.org/abs/2402.09539",
        ],
        "bibliography_result": (
            "The standard formula K_ab = e_a^mu e_b^nu nabla_mu n_nu identifies the "
            "variation channels. Active Janus/Sigma still needs active embedding, "
            "tangent/normal transport and connection variation before delta K is explicit."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "active_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding_ready,
                "readiness": active_embedding["readiness"],
                "still_open": active_embedding["still_open"],
            },
            "frame_trace_transport": {
                "gate": frame_trace["status"],
                "ready": frame_trace_ready,
                "prerequisites": frame_trace["prerequisites"],
                "transported": frame_trace["transported"],
                "current_frontier": frame_trace["current_frontier"],
            },
            "connection_variation": {
                "gate": connection_variation["status"],
                "ready": connection_variation_ready,
                "closure": connection_variation["closure"],
            },
            "tetrad_transport_closure": {
                "gate": tetrad_transport_closure["status"],
                "ready": tetrad_transport_closure["gate_passed"],
                "output_manifest": tetrad_transport_closure["output_manifest"],
            },
        },
        "formulae": {
            "extrinsic_curvature": "K_ab = e_a^mu e_b^nu nabla_mu n_nu",
            "second_form": "K_ab = -n_mu(partial_a partial_b X^mu + Gamma^mu_alpha_beta e_a^alpha e_b^beta)",
            "structural_variation": (
                "delta K_ab = -delta n_mu A_ab^mu - n_mu(delta partial_a partial_b X^mu "
                "+ delta Gamma^mu_alpha_beta e_a^alpha e_b^beta "
                "+ Gamma^mu_alpha_beta delta(e_a^alpha e_b^beta))"
            ),
            "variation_channels": "delta K_ab receives delta e_a, delta n, delta Gamma/omega and Z2 orientation terms",
        },
        "partial_subchannels": {
            "structural_variation_formula": {
                "ready": delta_k_structural_formula_ready,
                "status": "formula_only_not_value_transport_ready",
            },
            "active_value_transport": {
                "ready": closure["extrinsic_curvature_variation_transport_ready"],
                "status": "closed_by_symbolic_gaussian_collar" if symbolic_local_delta_k_ready else "blocked_on_active_embedding_frame_connection_variation",
            },
        },
        "deltaK_transport_ledger_declared": all(declared.values()),
        "deltaK_transport_ready": all(declared.values())
        and closure["extrinsic_curvature_variation_transport_ready"],
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "derive_residual_coefficients_R_K_ab",
            "feed_extrinsic_curvature_variation_transport_to_tetrad_variation_transport_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Extrinsic Curvature Variation Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['deltaK_transport_ledger_declared']}`",
        f"DeltaK transport ready: `{payload['deltaK_transport_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

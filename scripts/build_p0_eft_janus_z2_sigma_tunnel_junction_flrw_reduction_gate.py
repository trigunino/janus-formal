from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_junction_flrw_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_junction_flrw_reduction_gate.json")


def build_payload() -> dict:
    algebra = {
        "israel_junction_bibliography_checked": True,
        "z2_tunnel_junction_condition_derived": True,
        "tunnel_embedding_extrinsic_curvature_structural_ready": True,
        "FLRW_trace_reverse_algebra_declared": True,
        "junction_rho_projection_formula_ready": True,
        "junction_p_projection_formula_ready": True,
        "non_circular_use_of_junction_declared": True,
    }
    closure = {
        "DeltaK_s_of_a_ready": False,
        "DeltaK_tau_of_a_ready": False,
        "junction_rho_p_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-tunnel-junction-flrw-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel/Lanczos thin-shell junction formalism",
            "Singular hypersurfaces and thin shells in cosmology, arXiv:2402.09539",
            "generic extrinsic-curvature FLRW shell projections",
        ],
        "bibliography_result": (
            "The FLRW trace-reversed junction algebra is standard. The active Janus "
            "Z2/Sigma embedding functions and non-circular partition of T_eff_ab are local obligations."
        ),
        "algebra": algebra,
        "closure": closure,
        "formulas": {
            "junction_condition": "[K_ab - K h_ab]_Z2 = -kappa * T_Sigma_ab",
            "rho_junction": "rho_J(a) = 3 * eps_Z2 * DeltaK_s(a) / kappa",
            "p_junction": "p_J(a) = eps_Z2 * (DeltaK_tau(a) - 2 * DeltaK_s(a)) / kappa",
            "non_circular_policy": "do not solve the same junction equation twice as both definition and independent source",
        },
        "tunnel_junction_FLRW_algebra_ready": all(algebra.values()),
        "tunnel_junction_FLRW_closure_ready": all(algebra.values()) and all(closure.values()),
        "next_required": [
            "derive_DeltaK_s_of_a_and_DeltaK_tau_of_a_from_active_tunnel_embedding",
            "define_non_circular_partition_between_CartanGHY_and_junction_source",
            "reduce_tunnel_junction_source_to_rho_p_of_a_or_mark_as_constraint_only",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Tunnel Junction FLRW Reduction Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"FLRW algebra ready: `{payload['tunnel_junction_FLRW_algebra_ready']}`",
        f"FLRW closure ready: `{payload['tunnel_junction_FLRW_closure_ready']}`",
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

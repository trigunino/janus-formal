from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/resolved_throat_boundary_trace_targets.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_resolved_throat_boundary_trace_targets_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_resolved_throat_boundary_trace_targets_gate.json"
)


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    geometry_condition = {
        "Sigma_is_geometric_boundary_interface": True,
        "projective_Z2_identification_declared": True,
        "induced_metric_equivariant": "tau_Z2^* h_ab = h_ab",
        "normal_orientation_reversal": "tau_Z2^* n = -n",
        "extrinsic_curvature_reversal": "tau_Z2^* K_ab = -K_ab",
        "stationary_throat_condition": "delta_normal Area(Sigma) = 0",
        "flux_transparency_target": "F_a^Z2Sigma = 0 if stress is Z2-equivariant and tangential",
        "no_free_boundary_stress": True,
    }
    repo_sources = {
        "junction_condition_available": True,
        "junction_FLRW_algebra_available": True,
        "normal_flux_cancellation_ledger_available": True,
        "minimal_density_basis_available": True,
        "counterterm_trace_constraints_available": True,
    }
    trace_targets = {
        "R_Sigma_solution_certificate_supported_by_condition": True,
        "R_h_trace_required": True,
        "R_K_trace_required": True,
        "R_h_trace_derived": False,
        "R_K_trace_derived": False,
        "F_a_zero_derived_from_full_Z2_transparency": False,
    }
    payload = {
        "status": "janus-z2-sigma-resolved-throat-boundary-trace-targets-gate",
        "active_core": "Z2_tunnel_Sigma",
        "purpose": (
            "Convert the Janus resolved Z2 throat idea into concrete trace targets "
            "for the active Sigma counterterm closure."
        ),
        "bibliography_checked": [
            "Gibbons-Hawking-York boundary variational principle",
            "Lanczos-Israel/Darmois thin-shell junction conditions",
            "thin-shell wormhole throat stationarity/flare-out literature",
            "Janus projective S4/RP4 tunnel-resolution topology discussion",
        ],
        "geometry_condition": geometry_condition,
        "repo_sources": repo_sources,
        "trace_targets": trace_targets,
        "target_payload_written": True,
        "output_manifest": str(output_path),
        "gate_passed": False,
        "primary_blocker": "local_action_variation_trace_values",
        "blocked_reason": (
            "The Janus/Z2 throat condition fixes the geometric boundary problem, "
            "but it does not by itself emit numeric or symbolic values for "
            "R_h_trace and R_K_trace. Those traces must come from the local "
            "variation of the full Sigma action or an equivalent derived "
            "junction/stationarity equation."
        ),
        "next_required": [
            "derive_R_h_trace_from_variation_of_full_Sigma_boundary_action",
            "derive_R_K_trace_from_variation_of_full_Sigma_boundary_action",
            "prove_or_reject_F_a_zero_from_Z2_equivariant_tangential_stress",
            "feed_R_h_trace_R_K_trace_into_minimal_density_basis_constraints",
        ],
        "forbidden_shortcuts": [
            "do_not_assume_E_counterterm_zero",
            "do_not_fit_c1_c2_c3",
            "do_not_use_L_ct_oddness_to_prove_alpha_res_oddness",
        ],
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Resolved Throat Boundary Trace Targets Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Geometry Condition",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["geometry_condition"].items())
    lines.extend(["", "## Trace Targets"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["trace_targets"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

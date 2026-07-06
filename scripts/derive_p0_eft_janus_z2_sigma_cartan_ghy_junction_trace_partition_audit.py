from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_junction_trace_partition_audit.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_junction_trace_partition_audit.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_junction_trace_partition_audit.json"
)


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    round_throat = {
        "h_ab": "R^2 q_ab",
        "K_ab_plus": "+R q_ab",
        "K_ab_minus": "-R q_ab",
        "jump_K_ab": "2 R q_ab",
        "jump_K": "6/R",
    }
    junction_trace = {
        "jump_operator": "[K_ab - K h_ab]",
        "round_value": "-4 R q_ab",
        "trace": "-12/R",
        "junction_equation": "[K_ab - K h_ab] = -kappa_Z2Sigma S_ab",
        "surface_stress": "S_ab = 4 R q_ab / kappa_Z2Sigma",
        "surface_stress_trace": "S = 12/(kappa_Z2Sigma R)",
    }
    partition = {
        "finite_throat_trace_carried_by_junction": True,
        "finite_throat_trace_carried_by_Cartan_GHY_variation": True,
        "linear_K_counterterm_residual_after_partition": "0",
        "counterterm_c1_after_partition": "0",
        "counterterm_may_only_contain_non_GHY_residual": True,
    }
    payload = {
        "status": "janus-z2-sigma-cartan-ghy-junction-trace-partition-audit",
        "active_core": "Z2_tunnel_Sigma",
        "source": "symbolic_partition_derivation",
        "round_throat": round_throat,
        "junction_trace": junction_trace,
        "partition": partition,
        "linear_K_partition_closed": True,
        "R_h_trace_linear_K_residual_ready": True,
        "R_K_trace_linear_K_residual_ready": True,
        "R_h_trace_full_counterterm_ready": False,
        "R_K_trace_full_counterterm_ready": False,
        "E_counterterm_ready": False,
        "interpretation": (
            "The finite-throat trace target S=12/(kappa R) is exactly the "
            "Lanczos-Israel/Cartan-GHY jump trace on the round Z2 throat. "
            "Therefore the linear K piece is not an independent counterterm "
            "residual; after partition it sets c1=0 in L_ct."
        ),
        "next_required": [
            "subtract_linear_K_operator_from_counterterm_basis",
            "audit_remaining_non_GHY_residual_channels",
            "if_no_remaining_non_GHY_residual: prove_E_counterterm_zero_conditionally",
            "if_remaining_non_GHY_residual_exists: derive_its_local_density",
        ],
        "forbidden_shortcuts": [
            "do_not_duplicate_junction_trace_in_L_ct",
            "do_not_claim_full_E_counterterm_zero_from_linear_K_partition_only",
            "do_not_fit_remaining_c2_c3",
        ],
        "output_manifest": str(output_path),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY Junction Trace Partition Audit",
        "",
        payload["interpretation"],
        "",
        f"Linear K partition closed: `{payload['linear_K_partition_closed']}`",
        f"Full counterterm ready: `{payload['E_counterterm_ready']}`",
        "",
        "## Junction Trace",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["junction_trace"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

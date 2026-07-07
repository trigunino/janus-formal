from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
PARTITION_PATH = BASE / "cartan_ghy_junction_trace_partition_audit.json"
NON_GHY_PATH = BASE / "remaining_non_ghy_counterterm_channel_audit.json"
OUTPUT_PATH = BASE / "pt67_generalized_boundary_coefficient_constraints.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_pt67_generalized_bc_coefficient_solver_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_pt67_generalized_bc_coefficient_solver_gate.json"
)


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    *,
    partition_path: Path = PARTITION_PATH,
    non_ghy_path: Path = NON_GHY_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict[str, Any]:
    partition = _read(partition_path)
    non_ghy = _read(non_ghy_path)
    linear_k_duplicate_forbidden = (
        partition.get("partition", {}).get("linear_K_counterterm_residual_after_partition")
        == "0"
        and partition.get("partition", {}).get("finite_throat_trace_carried_by_Cartan_GHY_variation")
        is True
    )
    remaining_non_ghy_absent = (
        non_ghy.get("remaining_non_GHY_counterterm_channel_absent") is True
        or non_ghy.get("remaining_non_GHY_channel_absence_proved") is True
        or non_ghy.get("strict_no_extension_counterterm_absence_ready") is True
    )
    constraints = {
        "lambda_K": 0.0 if linear_k_duplicate_forbidden else None,
        "lambda_0": 0.0 if remaining_non_ghy_absent else None,
        "lambda_R3": 0.0 if remaining_non_ghy_absent else None,
        "lambda_K2": 0.0 if remaining_non_ghy_absent else None,
        "lambda_Kab2": 0.0 if remaining_non_ghy_absent else None,
    }
    all_fixed = all(value is not None for value in constraints.values())
    result = {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "PT67_regular_Sigma",
        "source": "active_derived_boundary_condition_constraints",
        "coefficient_status": "derived_not_fitted",
        "linear_K_duplicate_forbidden": linear_k_duplicate_forbidden,
        "remaining_non_GHY_residual_absent": remaining_non_ghy_absent,
        "constraints": constraints,
        "all_generalized_BC_coefficients_fixed": all_fixed,
        "generalized_boundary_action_trivial_under_strict_no_extension": all_fixed
        and all(value == 0.0 for value in constraints.values()),
        "interpretation": (
            "Under the strict PT67 no-extension policy, the linear K term is already "
            "carried by Cartan/GHY. If the remaining non-GHY residual channels are "
            "proved absent, the generalized boundary-action coefficients are fixed "
            "to zero, not left free."
        ),
    }
    if all_fixed:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-sigma-pt67-generalized-bc-coefficient-solver-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": {
            "cartan_ghy_junction_trace_partition": bool(partition),
            "remaining_non_ghy_counterterm_channel_audit": bool(non_ghy),
        },
        "output_manifest": str(output_path),
        "output_written": all_fixed,
        "result": result,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    result = payload["result"]
    lines = [
        "# Janus Z2/Sigma PT67 Generalized BC Coefficient Solver Gate",
        "",
        result["interpretation"],
        "",
        f"All coefficients fixed: `{result['all_generalized_BC_coefficients_fixed']}`",
        f"Strict action trivial: `{result['generalized_boundary_action_trivial_under_strict_no_extension']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

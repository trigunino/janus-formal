from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_junction_radial_block_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_junction_radial_block_gate.json")


def build_payload() -> dict:
    declared = {
        "Lanczos_Israel_bibliography_checked": True,
        "extrinsic_curvature_jump_declared": True,
        "Z2_normal_orientation_declared": True,
        "radial_junction_variation_declared": True,
        "trace_reversed_surface_equation_declared": True,
        "non_circular_partition_guard_declared": True,
        "observational_fit_forbidden": True,
        "E_tunnelJunction_functional_derivative_declared": True,
    }
    closure = {
        "E_tunnelJunction_structural_reduction_ready": True,
        "DeltaK_of_a_ready": False,
        "E_tunnelJunction_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-tunnel-junction-radial-block-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Lanczos-Israel thin-shell junction condition",
            "Poisson-Visser thin-shell wormhole radial equation of motion",
            "Darmois-Israel extrinsic-curvature jump formalism",
        ],
        "bibliography_result": (
            "Junction literature supplies the radial shell equation through the "
            "extrinsic-curvature jump. The Janus/Sigma function of scale factor still "
            "requires active DeltaK_s(a), DeltaK_tau(a), hence X_pm(a)."
        ),
        "declared": declared,
        "closure": closure,
        "structural_formula": (
            "E_tunnelJunction = delta_RSigma[ sqrt(|h|) * "
            "([K_ab] - h_ab [K] - kappa S_ab^Sigma) ] with Z2 normal orientation"
        ),
        "tunnel_junction_radial_ledger_declared": all(declared.values()),
        "tunnel_junction_radial_block_reduced": all(declared.values())
        and closure["E_tunnelJunction_structural_reduction_ready"],
        "tunnel_junction_radial_block_of_a_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "insert_active_DeltaK_s_of_a_and_DeltaK_tau_of_a",
            "insert_active_surface_stress_partition_without_double_counting",
            "evaluate_radial_junction_residual_on_Sigma",
            "propagate_E_tunnelJunction_into_E_RSigma_block_sum",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Tunnel-Junction Radial Block Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Block reduced: `{payload['tunnel_junction_radial_block_reduced']}`",
        f"Block of a ready: `{payload['tunnel_junction_radial_block_of_a_ready']}`",
        "",
        "## Structural Formula",
        f"`{payload['structural_formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

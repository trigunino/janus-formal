from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_density_expansion_gate import (
    build_payload as build_density_expansion_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_block_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_block_gate.json")


def build_payload() -> dict:
    density = build_density_expansion_payload()
    declared = {
        "boundary_counterterm_bibliography_checked": True,
        "Sigma_counterterm_uniqueness_imported": True,
        "counterterm_cancels_nonlinear_residual_imported": True,
        "counterterm_density_expansion_gate_declared": True,
        "counterterm_density_declared": True,
        "radial_counterterm_variation_declared": True,
        "Z2_orientation_sign_declared": True,
        "observational_fit_forbidden": True,
        "E_counterterm_functional_derivative_declared": True,
    }
    closure = {
        "counterterm_density_expansion_ready": density[
            "counterterm_density_expansion_ready"
        ],
        "explicit_counterterm_density_ready": density["closure"][
            "L_ct_ready_for_radial_variation"
        ],
        "E_counterterm_radial_block_reduced": False,
        "E_counterterm_of_a_ready": False,
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = (
        "none"
        if ready
        else density.get("primary_blocker", "counterterm_density_expansion_and_radial_variation")
    )
    return {
        "status": "janus-z2-sigma-counterterm-radial-block-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Brown-York boundary stress and counterterm methods",
            "Balasubramanian-Kraus boundary counterterm stress tensor",
            "active Janus Sigma nonlinear residual closure gate",
        ],
        "bibliography_result": (
            "Generic counterterm stress methods are available. The active Janus/Sigma "
            "counterterm is unique by the nonlinear residual closure, but its explicit "
            "radial density has not yet been expanded."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "density_expansion": {
                "gate": density["status"],
                "ready": density["counterterm_density_expansion_ready"],
                "current_frontier": density["current_frontier"],
                "primary_blocker": density.get("primary_blocker", "counterterm_density_expansion"),
            },
        },
        "structural_formula": (
            "E_counterterm = delta_RSigma S_ct[Sigma] "
            "= delta_RSigma integral_Sigma sqrt(|h|) L_ct(h,K,torsion,fields)"
        ),
        "counterterm_radial_ledger_declared": all(declared.values()),
        "counterterm_radial_block_reduced": all(declared.values()) and all(
            closure[key]
            for key in [
                "explicit_counterterm_density_ready",
                "E_counterterm_radial_block_reduced",
            ]
        ),
        "counterterm_radial_block_of_a_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "pass_counterterm_density_expansion_gate",
            "evaluate_delta_RSigma_of_sqrt_h_L_ct",
            "propagate_E_counterterm_into_E_RSigma_block_sum",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Radial Block Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_radial_ledger_declared']}`",
        f"Block reduced: `{payload['counterterm_radial_block_reduced']}`",
        "",
        "## Structural Formula",
        f"`{payload['structural_formula']}`",
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend([
        "",
        "## Next Required",
    ])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

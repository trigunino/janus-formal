from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate import (
    build_payload as build_local_density_basis_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate import (
    build_payload as build_residual_extraction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_density_expansion_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_density_expansion_gate.json")


def _first_blocker(*payloads: dict) -> str:
    for payload in payloads:
        blocker = payload.get("primary_blocker")
        if blocker and blocker != "none":
            return blocker
    return "counterterm_primitive_and_density_expansion"


def build_payload() -> dict:
    basis = build_local_density_basis_payload()
    residual = build_residual_extraction_payload()
    declared = {
        "Sigma_counterterm_uniqueness_imported": True,
        "counterterm_cancels_nonlinear_residual_imported": True,
        "counterterm_local_density_basis_gate_declared": True,
        "counterterm_residual_extraction_gate_declared": True,
        "density_expansion_problem_declared": True,
        "allowed_variables_declared": True,
        "no_new_counterterm_freedom_declared": True,
        "observational_fit_forbidden": True,
        "explicit_density_expansion_required": True,
    }
    closure = {
        "local_density_basis_complete": basis["closure"]["local_density_basis_complete"],
        "counterterm_primitive_integrated": residual["closure"][
            "counterterm_primitive_integrated"
        ],
        "L_ct_expanded_in_active_variables": residual["closure"][
            "L_ct_ready_for_density_expansion_gate"
        ],
        "L_ct_uniqueness_preserved": False,
        "L_ct_ready_for_radial_variation": False,
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none" if ready else _first_blocker(residual, basis)
    return {
        "status": "janus-z2-sigma-counterterm-density-expansion-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "active Janus Sigma nonlinear residual closure gate",
            "active counterterm local density basis gate",
            "active counterterm residual extraction gate",
            "Brown-York boundary counterterm stress method",
            "boundary counterterm renormalization literature",
        ],
        "bibliography_result": (
            "The active repository proves uniqueness/cancellation of the Sigma counterterm, "
            "while generic literature supplies variation methods. No external source expands "
            "the active Janus/Sigma counterterm density in local radial variables."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "local_density_basis": {
                "gate": basis["status"],
                "ready": basis["counterterm_local_density_basis_ready"],
                "closure": basis["closure"],
                "primary_blocker": basis.get("primary_blocker", "counterterm_local_density_basis"),
            },
            "residual_extraction": {
                "gate": residual["status"],
                "ready": residual["counterterm_residual_extraction_ready"],
                "current_frontier": residual["current_frontier"],
                "primary_blocker": residual.get("primary_blocker", "counterterm_residual_extraction"),
            },
        },
        "allowed_variables": [
            "h_ab",
            "K_ab",
            "Sigma torsion pullback",
            "Immirzi/radion boundary fields",
            "Z2 orientation sign",
        ],
        "forbidden": [
            "new fitted counterterm coefficient",
            "observational radius fit",
            "legacy Z4 counterterm import",
        ],
        "counterterm_density_expansion_ledger_declared": all(declared.values()),
        "counterterm_density_expansion_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "pass_counterterm_local_density_basis_gate",
            "pass_counterterm_residual_extraction_gate",
            "expand_L_ct_in_h_K_torsion_Immirzi_variables",
            "prove_expansion_preserves_unique_residual_cancellation",
            "pass_L_ct_to_counterterm_radial_block",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Density Expansion Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_density_expansion_ledger_declared']}`",
        f"Expansion ready: `{payload['counterterm_density_expansion_ready']}`",
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

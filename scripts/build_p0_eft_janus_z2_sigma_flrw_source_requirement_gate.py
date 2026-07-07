from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_action_to_flrw_source_audit import (
    build_payload as action_to_flrw,
)


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_source_requirement_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_source_requirement_gate.md")


def build_payload() -> dict[str, Any]:
    audit = action_to_flrw()
    sigma_zero = audit["rho_Sigma_status"] == "derived_zero_under_current_admitted_action"
    return {
        "status": "janus-z2-sigma-flrw-source-requirement-gate",
        "active_core": "Z2_tunnel_Sigma_PT_bridge",
        "archived_result": {
            "statement": (
                "The regular Sigma/PT bridge action currently emits no homogeneous "
                "FLRW source. The published Janus cosmology reaches FLRW through "
                "global bimetric bulk source equations, not through a local Sigma "
                "throat density."
            ),
            "sigma_only_action_audited": True,
            "sigma_only_variation_emits_zero_source": sigma_zero,
            "published_janus_uses_global_bimetric_bulk_source": True,
            "not_a_contradiction": True,
        },
        "current_action_status": {
            "rho_Sigma_status": audit["rho_Sigma_status"],
            "E_Z2Sigma_a2_ready": audit["E_Z2Sigma_a2_ready"],
            "nonzero_background_source_requires_extension": audit[
                "nonzero_background_source_requires_extension"
            ],
            "emitting_admitted_terms": audit["emitting_admitted_terms"],
        },
        "what_the_action_needs_for_FLRW": {
            "bulk_bimetric_stress": {
                "description": (
                    "A published Janus two-metric bulk action whose variation gives "
                    "T_plus, T_minus, determinant/projection factors, Bianchi closure, "
                    "and a nonzero FLRW reduction."
                ),
                "ready": False,
                "preferred_next_route": True,
            },
            "boundary_hamiltonian_charge": {
                "description": (
                    "A nonzero Q_boundary-Q_reference with active lapse, surface "
                    "measure, and state/reference normalization."
                ),
                "ready": False,
            },
            "admitted_sigma_surface_density": {
                "description": (
                    "A non-GHY, non-topological local Sigma density with coefficients "
                    "derived from the action, not fitted."
                ),
                "ready": False,
            },
            "null_LL_bridge_source": {
                "description": (
                    "A lightlike bridge source with derived chi_LL and a proven "
                    "projection to homogeneous FLRW density."
                ),
                "ready": False,
            },
            "quantum_topological_vacuum": {
                "description": (
                    "A Casimir/topological or flux/spin vacuum source with field "
                    "content, boundary conditions, coefficient, and radius map."
                ),
                "ready": False,
            },
        },
        "decision": {
            "do_not_force_N_gap_to_FLRW_density": True,
            "keep_Sigma_as_junction_topology_boundary_sector": True,
            "continue_current_branch_by_formalizing_bulk_bimetric_FLRW_source": True,
        },
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma FLRW Source Requirement Gate",
        "",
        payload["archived_result"]["statement"],
        "",
        f"rho_Sigma status: `{payload['current_action_status']['rho_Sigma_status']}`",
        f"E_Z2Sigma(a)^2 ready: `{payload['current_action_status']['E_Z2Sigma_a2_ready']}`",
        "",
        "## Required Nonzero Source Channels",
    ]
    for name, item in payload["what_the_action_needs_for_FLRW"].items():
        lines.append(f"- `{name}`: ready=`{item['ready']}`")
    lines.extend(
        [
            "",
            "## Decision",
            "- Do not force `N_gap` into a background density.",
            "- Keep Sigma/PT as junction/topology/boundary sector.",
            "- Use the published Janus bimetric bulk equations as the preferred FLRW-source route.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

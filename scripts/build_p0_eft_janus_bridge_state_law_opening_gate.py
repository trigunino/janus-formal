from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_bridge_state_law_opening_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_bridge_state_law_opening_gate.md"


def build_payload() -> dict[str, Any]:
    candidates = [
        {
            "id": "null_boundary_noether_charge",
            "state_object": "Q_bridge on the active Sigma/PT null boundary",
            "selection_target": "integrable boundary charge fixes M_bridge and chi_LL",
            "status": "best_geometric_charge_route",
            "missing": "active null boundary phase space, generator normalization, integrable charge",
        },
        {
            "id": "LL_worldvolume_flux_sector",
            "state_object": "integer flux and charge unit on the LL-brane worldvolume",
            "selection_target": "q_LL, F2_0, and primitive sector fix chi_LL",
            "status": "best_micro_tension_route",
            "missing": "Janus-derived q_LL, F2_0, compact cycle, primitive sector",
        },
        {
            "id": "PT_minimal_quantum_state",
            "state_object": "minimal nonzero PT-invariant bridge state",
            "selection_target": "PT state law rejects chi=0 and selects first allowed sector",
            "status": "best_quantum_state_route",
            "missing": "state space, inner product, Hamiltonian/charge operator, minimal-sector theorem",
        },
    ]
    return {
        "status": "janus-bridge-state-law-opening-gate",
        "branch": "janus_bridge_state_law",
        "core_statement": "alpha is treated as the bridge-state charge, not as a local coupling.",
        "charge_chain": "bridge state -> chi_LL -> R_s -> M_bridge -> alpha -> background observables",
        "rules": {
            "no_direct_alpha_fit": True,
            "no_invented_sigma_density": True,
            "no_legacy_Z4_shortcut": True,
            "observation_only_after_internal_state_law": True,
        },
        "candidate_routes": candidates,
        "working_definition": {
            "Sigma_PT_state_space": "boundary states compatible with PT and null bridge source",
            "chi_LL": "conserved bridge-state charge/tension",
            "nonzero_sector_condition": "chi_LL != 0 required for active bridge source",
        },
        "initial_verdict": "branch_opened_not_closed",
        "chi_LL_selected_no_fit": False,
        "next_concrete_gate": "AlphaBridgeStateLawCandidateDiscriminatorGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Bridge State Law Opening Gate",
        "",
        payload["core_statement"],
        "",
        f"Charge chain: `{payload['charge_chain']}`",
        f"Initial verdict: `{payload['initial_verdict']}`",
        f"chi_LL selected no-fit: `{payload['chi_LL_selected_no_fit']}`",
        "",
        "## Candidate Routes",
        "",
        "| Route | Status | Missing |",
        "|---|---|---|",
        *[
            f"| `{row['id']}` | `{row['status']}` | {row['missing']} |"
            for row in payload["candidate_routes"]
        ],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

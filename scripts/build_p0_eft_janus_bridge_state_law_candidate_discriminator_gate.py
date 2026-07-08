from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_bridge_state_law_candidate_discriminator_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_bridge_state_law_candidate_discriminator_gate.md"


def build_payload() -> dict[str, Any]:
    routes = [
        {
            "id": "null_boundary_noether_charge",
            "role": "defines the bridge charge and alpha map",
            "sufficient_alone": False,
            "missing": "active null boundary phase space and integrable generator",
        },
        {
            "id": "LL_worldvolume_flux_sector",
            "role": "turns chi_LL into a discrete flux/tension sector",
            "sufficient_alone": False,
            "missing": "Janus-derived q_LL, F2_0, compact cycle and area gauge",
        },
        {
            "id": "PT_minimal_quantum_state",
            "role": "selects the primitive nonzero sector once the lattice exists",
            "sufficient_alone": False,
            "missing": "PT Hilbert/state law and primitive-sector theorem",
        },
    ]
    return {
        "status": "janus-bridge-state-law-candidate-discriminator",
        "best_intuition": "no single route closes alpha; the non-rustine path is composite",
        "composite_path": [
            "derive Q_bridge from the null/PT boundary symplectic structure",
            "derive chi_LL flux/tension lattice from the LL worldvolume sector",
            "derive PT primitive nonzero state selection",
            "map Q_bridge/chi_LL -> M_bridge -> alpha -> background",
        ],
        "routes": routes,
        "rules": {
            "no_direct_alpha_fit": True,
            "no_observation_sector_selection_yet": True,
            "no_invented_sigma_density": True,
            "no_single_route_promotion": True,
        },
        "next_gate": "P0EFTJanusBridgeStateLawCompositeClosureGate",
        "chi_LL_selected_no_fit": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Bridge State Law Candidate Discriminator",
        "",
        payload["best_intuition"],
        "",
        "## Composite path",
        "",
        *[f"- {step}" for step in payload["composite_path"]],
        "",
        "## Route roles",
        "",
        "| Route | Role | Sufficient alone | Missing |",
        "|---|---|---:|---|",
        *[
            f"| `{row['id']}` | {row['role']} | `{row['sufficient_alone']}` | {row['missing']} |"
            for row in payload["routes"]
        ],
        "",
        f"Next gate: `{payload['next_gate']}`",
        f"chi_LL selected no-fit: `{payload['chi_LL_selected_no_fit']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

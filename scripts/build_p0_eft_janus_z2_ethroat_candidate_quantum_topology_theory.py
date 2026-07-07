from __future__ import annotations

import json
import math
from pathlib import Path


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_ethroat_candidate_quantum_topology_theory.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_ethroat_candidate_quantum_topology_theory.md"


def _candidate_values(n: int, gamma: float = 1.0) -> dict:
    # Planck units keep this frontier independent of CODATA convention.
    area_gap_lP2 = 8.0 * math.pi * gamma
    area_lP2 = n * area_gap_lP2
    radius_lP = math.sqrt(area_lP2 / (4.0 * math.pi))
    # With L = R and alpha_time = L/c, E_mass = -L*c/(2*pi*G).
    # In Planck mass units this is -L/(2*pi*lP).
    ethroat_mPlanck = -radius_lP / (2.0 * math.pi)
    return {
        "N": n,
        "gamma": gamma,
        "A_gap_over_lP2": area_gap_lP2,
        "A_sigma_over_lP2": area_lP2,
        "L_over_lP": radius_lP,
        "alpha_over_tP": radius_lP,
        "E_throat_over_mP": ethroat_mPlanck,
    }


def build_payload() -> dict:
    primitive = _candidate_values(1)
    macroscopic_examples = [_candidate_values(n) for n in [10**10, 10**60, 10**122]]
    return {
        "status": "janus-z2-ethroat-candidate-quantum-topology-theory",
        "active_core": "S4_L_to_RP4_L_resolved_by_Sigma",
        "candidate_name": "quantized_throat_area_flux_sector",
        "new_physical_postulates": [
            "Sigma carries a genuine quantum boundary Hilbert/phase space",
            "the throat area/flux spectrum is A_Sigma = N * A_gap",
            "the Janus global scale is L = sqrt(A_Sigma/(4*pi))",
            "E_throat equals E_global and alpha_time = L/c",
        ],
        "derived_relations_in_candidate": {
            "A_sigma": "N * A_gap",
            "L": "sqrt(A_sigma/(4*pi))",
            "alpha_time": "L/c",
            "H0": "h_shape(u0)/alpha_time",
            "E_throat_mass": "-L*c/(2*pi*G)",
        },
        "primitive_sector_N1": primitive,
        "macroscopic_sector_examples": macroscopic_examples,
        "does_primitive_N1_give_cosmological_scale": False,
        "does_discrete_family_exist": True,
        "does_candidate_select_unique_N": False,
        "why_unique_N_not_selected": (
            "Topology supplies integrality but not the occupation number N. "
            "Small topological invariants select O(1) sectors, giving Planck-scale "
            "L. Cosmological L requires a huge N or an additional state law."
        ),
        "candidate_no_fit_alpha_ready": False,
        "candidate_status": "coherent_new_quantum_topology_layer_but_not_unique_selector",
        "what_would_close_it": [
            "derive N from a Janus/PT irreducibility theorem",
            "derive N from a global state-counting or entropy extremum",
            "derive A_gap/gamma from the Janus action rather than importing it",
            "prove the throat quantum area equals the cosmological S4_L scale",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    p = payload["primitive_sector_N1"]
    lines = [
        "# Janus Z2 E_throat Candidate Quantum/Topology Theory",
        "",
        f"Candidate: `{payload['candidate_name']}`",
        f"Status: `{payload['candidate_status']}`",
        f"Discrete family exists: `{payload['does_discrete_family_exist']}`",
        f"Unique N selected: `{payload['does_candidate_select_unique_N']}`",
        f"No-fit alpha ready: `{payload['candidate_no_fit_alpha_ready']}`",
        "",
        "## Core Relations",
    ]
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["derived_relations_in_candidate"].items()
    )
    lines.extend(
        [
            "",
            "## Primitive Sector",
            "",
            f"- `N=1` gives `L/lP = {p['L_over_lP']:.6g}`",
            f"- `E_throat/mP = {p['E_throat_over_mP']:.6g}`",
            "- This is Planck-scale, not cosmological.",
            "",
            "## Verdict",
            "",
            payload["why_unique_N_not_selected"],
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

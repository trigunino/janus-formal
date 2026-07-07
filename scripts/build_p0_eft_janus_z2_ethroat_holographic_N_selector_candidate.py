from __future__ import annotations

import json
import math
from pathlib import Path


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_ethroat_holographic_N_selector_candidate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_ethroat_holographic_N_selector_candidate.md"

C_KM_S = 299792.458
MPC_KM = 3.0856775814913673e19
T_PLANCK_S = 5.391247e-44


def _u0_from_q0(q0: float) -> float:
    return math.asinh(math.sqrt(-1.0 / (2.0 * q0)))


def _h_shape(u: float) -> float:
    return math.sinh(2.0 * u) / (math.cosh(u) ** 4)


def _N_required(q0: float, H0_km_s_Mpc: float, gamma: float = 1.0) -> dict:
    u0 = _u0_from_q0(q0)
    h = _h_shape(u0)
    H0_s = H0_km_s_Mpc / MPC_KM
    alpha_s = h / H0_s
    L_over_lP = alpha_s / T_PLANCK_S
    N = (L_over_lP**2) / (2.0 * gamma)
    return {
        "q0": q0,
        "H0_km_s_Mpc": H0_km_s_Mpc,
        "gamma": gamma,
        "u0": u0,
        "h_shape_u0": h,
        "alpha_s": alpha_s,
        "L_over_lP": L_over_lP,
        "N_required": N,
    }


def build_payload() -> dict:
    cases = {
        "published_janus_q0": _N_required(-0.087, 70.0),
        "SN_diag_best_q0": _N_required(-0.03512140175219025, 70.0),
        "BAO_boundary_q0": _N_required(-0.001, 70.0),
    }
    routes = {
        "cosmological_horizon_entropy": {
            "formula": "N ~ A_H/(4 lP^2) ~ pi/(H0^2 tP^2)",
            "gets_10_120": True,
            "selects_N_without_H0": False,
            "verdict": "explains magnitude after H0 is known; circular as H0 predictor",
        },
        "de_sitter_area_bits": {
            "formula": "N_bits ~ A_dS/lP^2",
            "gets_10_120": True,
            "selects_N_without_H0": False,
            "verdict": "same H0/L input in holographic language",
        },
        "collective_graviton_condensate": {
            "formula": "N ~ (L/lP)^2",
            "gets_10_120": True,
            "selects_N_without_L": False,
            "verdict": "natural occupation interpretation, but L remains input",
        },
        "primitive_topological_sector": {
            "formula": "N=O(1)",
            "gets_10_120": False,
            "selects_N_without_H0": True,
            "verdict": "non-circular but gives Planck-scale universe",
        },
    }
    return {
        "status": "janus-z2-ethroat-holographic-N-selector-candidate",
        "active_core": "S4_L_to_RP4_L_resolved_by_Sigma",
        "target_N_order": "10^120",
        "required_N_cases": cases,
        "candidate_routes": routes,
        "best_physical_interpretation": (
            "N is naturally an area/entropy/occupation number of the cosmological "
            "throat. This explains why it is huge, but does not predict it unless "
            "an independent entropy/state law fixes N without using H0 or L."
        ),
        "holographic_N_selector_ready": False,
        "non_circular_selector_found": False,
        "new_law_needed": (
            "A Janus-specific microcanonical or holographic state law selecting "
            "the throat entropy/occupation number N."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    pub = payload["required_N_cases"]["published_janus_q0"]
    lines = [
        "# Janus Z2 E_throat Holographic N Selector Candidate",
        "",
        f"Target N order: `{payload['target_N_order']}`",
        f"Published Janus q0 case N: `{pub['N_required']:.6e}`",
        f"Holographic selector ready: `{payload['holographic_N_selector_ready']}`",
        f"Non-circular selector found: `{payload['non_circular_selector_found']}`",
        "",
        "## Route Verdicts",
    ]
    for name, route in payload["candidate_routes"].items():
        lines.append(
            f"- `{name}`: gets_10^120=`{route['gets_10_120']}`; "
            f"verdict={route['verdict']}"
        )
    lines.extend(["", "## Interpretation", "", payload["best_physical_interpretation"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

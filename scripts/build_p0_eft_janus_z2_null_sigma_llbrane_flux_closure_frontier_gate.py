from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_gauge_sector_derivability_gate import (
    build_payload as build_gauge_derivability,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_minimal_gauge_action_reducer_gate import (
    build_payload as build_action_reducer,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_s2_flux_topology_gate import (
    build_payload as build_s2_topology,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_flux_closure_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_flux_closure_frontier_gate.json"
)


def build_payload() -> dict:
    topology = build_s2_topology()
    action = build_action_reducer()
    gauge = build_gauge_derivability()

    closed = {
        "S2_flux_integer_sector_supported": topology["topology_gate_passed"],
        "chi_composite_and_conserved": gauge["derived_now"][
            "chi_LL_is_modified_measure_composite"
        ]
        and gauge["derived_now"]["gauge_EOM_conserves_dual_measure_flux_locally"],
        "PT_negative_sign_and_bridge_matching": gauge["derived_now"][
            "PT_fixes_chi_sign_negative"
        ]
        and gauge["derived_now"]["bridge_matching_gives_Rs_from_chi"],
        "F2_reduction_formula_available": True,
    }
    remaining = {
        "q_LL": {
            "status": "not_closed",
            "why": (
                "U(1) flux topology gives n, but charge normalization requires a "
                "worldvolume gauge coupling or charged-defect normalization."
            ),
            "clean_exits": [
                "derive minimal LL charge from action",
                "declare q_LL as extension-state/gauge-sector coupling",
            ],
        },
        "dimensionful_F2_0": {
            "status": "not_closed",
            "why": (
                "F2*dL/dF2=1/8 reduces F2_0 only after L(F2) and its dimensional "
                "normalization are derived."
            ),
            "clean_exits": [
                "derive dimensionful monomial coupling lambda_F2",
                "derive area/length scale converting auxiliary F2 to m^-4",
            ],
        },
        "physical_area_gauge": {
            "status": "not_closed",
            "why": (
                "LL auxiliary metric is not automatically the physical induced "
                "S2 metric; the conversion factor must be fixed by EOM or boundary "
                "gauge condition."
            ),
            "clean_exits": [
                "prove physical_induced_S2_metric gauge from LL constraints",
                "derive explicit auxiliary-to-physical area conversion factor",
            ],
        },
    }
    ready_for_numeric_chi = (
        all(closed.values())
        and topology["chi_selection_gate_passed"]
        and action["dimensionful_F2_0_ready"]
    )
    return {
        "status": "janus-z2-null-sigma-llbrane-flux-closure-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "closed_without_rustine": closed,
        "remaining_independent_theory_inputs": remaining,
        "minimal_remaining_count": len(remaining),
        "ready_for_numeric_chi_LL": ready_for_numeric_chi,
        "next_best_single_move": (
            "derive/adopt the LL gauge-sector action normalization, because it "
            "can simultaneously fix q_LL and dimensionful F2_0 if the action is "
            "strong enough"
        ),
        "observation_allowed_now": False,
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Flux Closure Frontier Gate",
        "",
        f"Ready for numeric chi_LL: `{payload['ready_for_numeric_chi_LL']}`",
        f"Observation allowed now: `{payload['observation_allowed_now']}`",
        f"Minimal remaining count: `{payload['minimal_remaining_count']}`",
        "",
        "## Closed Without Rustine",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closed_without_rustine"].items())
    lines.extend(["", "## Remaining Independent Theory Inputs"])
    lines.extend(f"- `{key}`: {value['why']}" for key, value in payload["remaining_independent_theory_inputs"].items())
    lines.extend(["", f"Next best single move: {payload['next_best_single_move']}"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_uv_scale_candidate_gate import (
    build_payload as build_uv_candidates,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_uv_no_go_exit_conditions_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_uv_no_go_exit_conditions_gate.json")


def build_payload() -> dict:
    uv = build_uv_candidates()
    necessary_conditions = {
        "dimensionful_scale_available": True,
        "scale_identified_with_throat_geometry": False,
        "scale_enters_LL_or_Sigma_action": False,
        "normalization_to_chi_LL_derived": False,
        "non_observational_provenance": False,
    }
    forbidden_shortcuts = {
        "set_Rs_equal_lP_by_choice": True,
        "use_area_gap_without_throat_area_theorem": True,
        "use_Holst_gamma_as_length": True,
        "use_Nieh_Yan_boundary_term_as_density_without_state": True,
        "fit_chi_LL_to_H0_or_BAO": True,
    }
    admissible_exits = {
        "area_gap_exit": {
            "required": [
                "quantum_area_spectrum_adopted_or_derived",
                "A_Sigma = N_gap * A_gap theorem",
                "physical induced-area gauge",
                "LL matching chi_LL = -1/(8*pi*R_s)",
            ],
            "ready": False,
        },
        "spin_condensate_exit": {
            "required": [
                "active spin current on Sigma",
                "Einstein-Cartan/Holst torsion constraint solved",
                "fermion density or condensate state derived",
                "projection to LL throat stress/tension",
            ],
            "ready": False,
        },
        "UV_LL_action_exit": {
            "required": [
                "microscopic LL worldvolume action",
                "q_LL normalization",
                "dimensionful F2_0 or lambda_F2 from action",
                "physical S2 area gauge",
            ],
            "ready": False,
        },
        "state_charge_exit": {
            "required": [
                "Noether/Souriau mass Casimir",
                "PT-compatible bridge matching",
                "Q_Sigma = M_bridge*c^2 theorem",
                "non-observational state selection",
            ],
            "ready": False,
        },
    }
    no_go_holds = not all(necessary_conditions.values())
    return {
        "status": "janus-z2-chi-ll-uv-no-go-exit-conditions-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "uv_candidate_gate_status": uv["status"],
        "necessary_conditions_for_uv_prediction": necessary_conditions,
        "forbidden_shortcuts": forbidden_shortcuts,
        "admissible_non_rustine_exits": admissible_exits,
        "no_go_statement": (
            "A constructible UV scale cannot predict chi_LL unless it is "
            "identified with the active throat geometry, enters the LL/Sigma "
            "action, and is normalized to chi_LL with non-observational provenance."
        ),
        "no_go_holds_for_current_workspace": no_go_holds,
        "chi_LL_prediction_ready": False,
        "search_space_reduced_to": list(admissible_exits.keys()),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL UV No-Go and Exit Conditions Gate",
        "",
        payload["no_go_statement"],
        "",
        f"No-go holds now: `{payload['no_go_holds_for_current_workspace']}`",
        f"chi_LL prediction ready: `{payload['chi_LL_prediction_ready']}`",
        "",
        "## Necessary Conditions",
    ]
    lines.extend(
        f"- `{name}`: `{value}`"
        for name, value in payload["necessary_conditions_for_uv_prediction"].items()
    )
    lines.extend(["", "## Admissible Exits"])
    for name, data in payload["admissible_non_rustine_exits"].items():
        lines.append(f"- `{name}`: ready=`{data['ready']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

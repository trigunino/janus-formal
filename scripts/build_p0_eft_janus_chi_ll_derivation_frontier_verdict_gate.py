from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_ll_flux_chi_quantization_gate import build_payload as build_flux
from scripts.build_p0_eft_janus_pt_boundary_chi_stationarity_gate import (
    build_payload as build_pt,
)
from scripts.build_p0_eft_janus_z2_chi_ll_will_action_power_selection_gate import (
    build_payload as build_will,
)
from scripts.build_p0_eft_janus_z2_cover_master_llbrane_action_extension_gate import (
    build_payload as build_llbrane,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_chi_ll_derivation_frontier_verdict_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_chi_ll_derivation_frontier_verdict_gate.md"


def build_payload() -> dict[str, Any]:
    llbrane = build_llbrane()
    pt = build_pt()
    flux = build_flux()
    will = build_will()
    closed = {
        "LL_brane_relation": llbrane["closure"]["mass_radius_relation_derived"],
        "PT_boundary_stationarity": pt["gate_passed"],
        "LL_flux_quantization_equations": flux["gate_passed"],
        "WILL_action_power_p_half": will["WILL_power_selection_ready"],
    }
    still_missing = {
        "q_LL_charge_unit": "not derived",
        "F2_0_absolute_value": "not derived",
        "lambda_F2_absolute_normalization": "not derived",
        "primitive_N_gap_or_boundary_state": "not derived",
        "background_source_map_E_Z2Sigma": "not derived",
    }
    return {
        "status": "janus-chi-ll-derivation-frontier-verdict-gate",
        "closed_subresults": closed,
        "still_missing": still_missing,
        "chi_LL_selected_no_fit": False,
        "frontier_reduced_to": "worldvolume_charge_normalization_or_boundary_state_law",
        "do_not_repeat": [
            "LL-brane mass-radius relation",
            "PT symmetry-only stationarity",
            "Chern primitive flux no-go",
            "WILL p=1/2 action power selection",
        ],
        "only_real_next_moves": [
            "derive q_LL from a Janus worldvolume gauge principle",
            "derive a PT boundary state that fixes primitive N_gap/charge",
            "accept chi_LL as explicit state sector and test observationally with no no-fit claim",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus chi_LL Derivation Frontier Verdict",
        "",
        f"chi_LL selected no-fit: `{payload['chi_LL_selected_no_fit']}`",
        f"Frontier reduced to: `{payload['frontier_reduced_to']}`",
        "",
        "## Closed Subresults",
        *[f"- `{key}`: `{value}`" for key, value in payload["closed_subresults"].items()],
        "",
        "## Still Missing",
        *[f"- `{key}`: {value}" for key, value in payload["still_missing"].items()],
        "",
        "## Only Real Next Moves",
        *[f"- {item}" for item in payload["only_real_next_moves"]],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

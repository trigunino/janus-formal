from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_composite_closure_route_gate import (
    build_payload as build_composite,
)
from scripts.build_p0_eft_janus_z2_chi_ll_option_evaluation_matrix import (
    build_payload as build_options,
)
from scripts.build_p0_eft_janus_z2_cover_master_llbrane_action_extension_gate import (
    build_payload as build_llbrane,
)
from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit import (
    build_payload as build_flux,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_chi_ll_selection_reprise_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_chi_ll_selection_reprise_gate.md"


def build_payload() -> dict[str, Any]:
    llbrane = build_llbrane()
    options = build_options()
    flux = build_flux()
    composite = build_composite()

    done = {
        "LL_brane_worldvolume_added": llbrane["closure"]["LL_brane_worldvolume_added_on_Sigma"],
        "mass_radius_relation_derived": llbrane["closure"]["mass_radius_relation_derived"],
        "discrete_sector_family_ready": composite["N_gap_family_ready"],
        "discrete_sector_scan_ready": composite["discrete_sector_scan_ready"],
        "primitive_flux_standard_no_go": composite["primitive_flux_standard_no_go"],
    }
    remaining = {
        "chi_selected_by_global_variation": llbrane["closure"][
            "chi_magnitude_selected_by_global_variation"
        ],
        "chi_selected_by_boundary_state": llbrane["closure"][
            "chi_magnitude_selected_by_boundary_state"
        ],
        "primitive_flux_law_ready": flux["primitive_flux_sector_law_ready"],
        "unit_flux_irreducibility_ready": flux["unit_flux_irreducibility_ready"],
        "N_gap_to_background_source_ready": composite["N_gap_to_background_source_ready"],
    }
    candidate_next = [
        {
            "id": "PT_boundary_state_selects_chi",
            "status": "not_yet_derived",
            "minimal_new_object": "PT-invariant boundary state functional whose stationarity fixes chi_LL",
            "why": "directly targets the missing chi magnitude selection in the LL-brane action extension",
        },
        {
            "id": "LL_auxiliary_flux_quantizes_chi",
            "status": "not_yet_derived",
            "minimal_new_object": "LL worldvolume gauge sector with charge unit and compact cycle",
            "why": "can discretize chi_LL, but previous primitive flux audit shows Chern topology alone is insufficient",
        },
    ]

    return {
        "status": "janus-chi-ll-selection-reprise-gate",
        "already_done": done,
        "remaining_blockers": remaining,
        "option_matrix_recommended_order": options["recommended_order"],
        "candidate_next_minimal_routes": candidate_next,
        "chi_LL_selected_no_fit": any(remaining.values()),
        "remaining_blocker_is_selection_law": True,
        "avoid_duplication": [
            "do not redo discrete N_gap scan",
            "do not redo primitive flux no-go",
            "do not redo LL-brane mass-radius relation",
        ],
        "best_next_target": "PT_boundary_state_selects_chi",
        "reason_for_best_next": (
            "Flux quantization was already blocked by primitive-sector irreducibility. "
            "The cleanest untested step is a PT boundary-state stationarity law for chi_LL."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus chi_LL Selection Reprise Gate",
        "",
        f"chi_LL selected no-fit: `{payload['chi_LL_selected_no_fit']}`",
        f"Best next target: `{payload['best_next_target']}`",
        "",
        "## Already Done",
        *[f"- `{key}`: `{value}`" for key, value in payload["already_done"].items()],
        "",
        "## Remaining Blockers",
        *[f"- `{key}`: `{value}`" for key, value in payload["remaining_blockers"].items()],
        "",
        "## Avoid Duplication",
        *[f"- {item}" for item in payload["avoid_duplication"]],
        "",
        payload["reason_for_best_next"],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

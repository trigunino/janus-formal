from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_ethroat_non_circular_N_frontier_gate import (
    build_payload as non_circular_frontier,
)
from scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate import (
    build_payload as chern_su2_bridge,
)
from scripts.build_p0_eft_janus_z2_sigma_ngap_selection_law_registry import (
    build_payload as ngap_registry,
)
from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit import (
    build_payload as primitive_flux_audit,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_ethroat_remaining_non_circular_frontiers_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_ethroat_remaining_non_circular_frontiers_gate.md"


def _blocked_by(items: dict[str, bool]) -> list[str]:
    return [key for key, value in items.items() if not value]


def build_payload() -> dict[str, Any]:
    frontier = non_circular_frontier()
    registry = ngap_registry()
    primitive = primitive_flux_audit()
    bridge = chern_su2_bridge()

    microcanonical_conditions = {
        "boundary_phase_space_derived_from_Janus_Sigma": False,
        "boundary_Hilbert_space_HSigma_derived": False,
        "microcanonical_constraint_derived_without_H0_L_alpha": False,
        "dim_HSigma_or_entropy_formula_available": False,
        "state_law_selects_macro_N_without_observation": False,
        "N_to_E_throat_map_already_available": True,
    }
    tqft_conditions = {
        "TQFT_boundary_theory_derived_from_Janus_action": False,
        "gauge_group_derived_not_chosen": bridge["chern_to_su2_puncture_bridge_ready"],
        "level_k_derived_without_area_or_H0": False,
        "primitive_flux_or_puncture_sector_derived": primitive["N_gap_equals_abs_n_derived"],
        "partition_function_selects_macro_N_without_observation": False,
        "N_to_E_throat_map_already_available": True,
    }
    micro_ready = all(microcanonical_conditions.values())
    tqft_ready = all(tqft_conditions.values())
    return {
        "status": "janus-z2-ethroat-remaining-non-circular-frontiers-gate",
        "active_core": "S4_L_to_RP4_L_resolved_by_Sigma",
        "target_N": "O(10^120)",
        "previous_frontier_verdict": frontier["frontier_verdict"],
        "ngap_registry_status": registry["current_best_status"],
        "microcanonical_boundary_hilbert_space": {
            "physical_meaning": (
                "Sigma has a finite quantum boundary Hilbert space; a "
                "microcanonical law selects a macro-entropy or occupation N."
            ),
            "non_circular_if_closed": True,
            "conditions": microcanonical_conditions,
            "ready": micro_ready,
            "blocked_by": _blocked_by(microcanonical_conditions),
            "classification": "new_state_law_required",
        },
        "janus_derived_tqft_level": {
            "physical_meaning": (
                "Sigma carries a Janus-derived boundary TQFT, e.g. CS-like; "
                "the action fixes its level and allowed sectors."
            ),
            "non_circular_if_closed": True,
            "conditions": tqft_conditions,
            "ready": tqft_ready,
            "blocked_by": _blocked_by(tqft_conditions),
            "classification": "new_boundary_TQFT_or_level_law_required",
        },
        "bibliography_result": [
            {
                "key": "Engle-Noui-Perez-2009",
                "result": "SU(2) Chern-Simons horizon state counting uses Hilbert spaces on a punctured sphere; it needs boundary conditions, level and puncture labels.",
                "url": "https://arxiv.org/abs/0905.3168",
            },
            {
                "key": "Isolated-horizon-LQG-reviews",
                "result": "The horizon Hilbert space and microcanonical counting are standard once area/level/punctures are supplied; they do not derive a Janus scale by themselves.",
                "url": "https://arxiv.org/abs/1112.0291",
            },
            {
                "key": "Primitive-flux-audit",
                "result": "Total Chern charge does not force N_gap=|n| without an extra primitive sector law.",
                "url": str(Path("outputs/reports/p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit.md")),
            },
        ],
        "accepted_non_circular_selector": None,
        "N_selected_non_circularly": micro_ready or tqft_ready,
        "hard_conclusion": (
            "Both remaining routes are coherent research programs, not current "
            "Janus derivations. The microcanonical route needs a Janus-derived "
            "boundary Hilbert space and state law. The TQFT route needs a "
            "Janus-derived boundary theory, level and primitive sector. Without "
            "one of these, N remains a sector label, not a no-fit prediction."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 E_throat Remaining Non-Circular Frontiers Gate",
        "",
        f"Target N: `{payload['target_N']}`",
        f"N selected non-circularly: `{payload['N_selected_non_circularly']}`",
        "",
        "## Microcanonical Boundary Hilbert Space",
        f"Ready: `{payload['microcanonical_boundary_hilbert_space']['ready']}`",
        "Blocked by:",
    ]
    lines.extend(f"- `{item}`" for item in payload["microcanonical_boundary_hilbert_space"]["blocked_by"])
    lines.extend(
        [
            "",
            "## Janus-Derived TQFT / Level",
            f"Ready: `{payload['janus_derived_tqft_level']['ready']}`",
            "Blocked by:",
        ]
    )
    lines.extend(f"- `{item}`" for item in payload["janus_derived_tqft_level"]["blocked_by"])
    lines.extend(["", "## Conclusion", "", payload["hard_conclusion"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

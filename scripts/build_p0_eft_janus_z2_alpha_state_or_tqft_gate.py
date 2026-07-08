from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from scripts.build_p0_eft_janus_z2_ethroat_remaining_non_circular_frontiers_gate import (
    build_payload as build_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_alpha_selection_law_closure_gate import (
    build_payload as build_selection_law_payload,
)

REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_alpha_state_or_tqft_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_alpha_state_or_tqft_gate.md"


def _pick_selected_route(frontier: dict[str, Any]) -> str:
    micro_ready = bool(frontier["microcanonical_boundary_hilbert_space"]["ready"])
    tqft_ready = bool(frontier["janus_derived_tqft_level"]["ready"])
    if micro_ready and tqft_ready:
        return "ambiguous"
    if micro_ready:
        return "microcanonical"
    if tqft_ready:
        return "tqft"
    return "none"


def build_payload(*, force_microcanonical: bool | None = None, force_tqft: bool | None = None) -> dict[str, Any]:
    frontier = build_frontier_payload()
    selection = build_selection_law_payload()

    micro_ready = bool(frontier["microcanonical_boundary_hilbert_space"]["ready"])
    tqft_ready = bool(frontier["janus_derived_tqft_level"]["ready"])
    if force_microcanonical is not None:
        micro_ready = force_microcanonical
    if force_tqft is not None:
        tqft_ready = force_tqft

    selected_route = _pick_selected_route(
        {
            "microcanonical_boundary_hilbert_space": {"ready": micro_ready},
            "janus_derived_tqft_level": {"ready": tqft_ready},
        }
    )

    micro_blockers = list(frontier["microcanonical_boundary_hilbert_space"]["blocked_by"])
    tqft_blockers = list(frontier["janus_derived_tqft_level"]["blocked_by"])

    non_circular_selector_ready = micro_ready or tqft_ready
    state_sector_fallback = not non_circular_selector_ready

    return {
        "status": "janus-z2-alpha-state-or-tqft-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "selected_route": selected_route,
        "selected_non_circular_gate": (
            "microcanonical_boundary_state_law"
            if selected_route == "microcanonical"
            else "tqft_boundary_action" if selected_route == "tqft" else None
        ),
        "state_sector_fallback": state_sector_fallback,
        "non_circular_selector_ready": non_circular_selector_ready,
        "microcanonical_route_ready": micro_ready,
        "tqft_route_ready": tqft_ready,
        "route_blocked_by": {
            "microcanonical": micro_blockers,
            "tqft": tqft_blockers,
        },
        "selection_law_unique_alpha_derivable": bool(selection["unique_alpha_selector_derived"]),
        "alpha_state_sector_remains_required": bool(selection["alpha_state_sector_remains_required"]),
        "non_fitted_interpretation": (
            "alpha_m is a global state/integration constant unless one route is fully derived. "
            "Both non-circular selectors stay blocked without explicit boundary-law or "
            "Janus-derived TQFT level primitives."
        ),
        "next_steps": {
            "microcanonical": "derive boundary Hilbert space + microcanonical state law on Sigma/PT (not by fit)",
            "tqft": "derive Janus boundary action/theory + CS level + primitive sector map",
            "state_sector": (
                "keep alpha as non-circular sector label and compare with observation only under fixed policy"
            ),
        },
        "gate_passed": True,
    }


def write_reports(*args: object, **kwargs: object) -> dict[str, Any]:
    payload = build_payload(*args, **kwargs)
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha State-or-TQFT Selection Gate",
        "",
        f"Selected route: `{payload['selected_route']}`",
        f"State-sector fallback: `{payload['state_sector_fallback']}`",
        f"Non-circular selector ready: `{payload['non_circular_selector_ready']}`",
        f"Unique alpha selector derived: `{payload['selection_law_unique_alpha_derivable']}`",
        "",
        payload["non_fitted_interpretation"],
        "",
        "## Next steps",
        f"- Microcanonical: `{payload['next_steps']['microcanonical']}`",
        f"- TQFT route: `{payload['next_steps']['tqft']}`",
        f"- State sector policy: `{payload['next_steps']['state_sector']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

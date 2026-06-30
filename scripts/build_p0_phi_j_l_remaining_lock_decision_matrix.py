from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_equations_to_phi_selector_probe import (
    build_payload as build_janus_selector,
)
from scripts.build_p0_b4vol_jacobian_gauge_degeneracy_proof import (
    build_payload as build_b4vol_degeneracy,
)
from scripts.build_p0_lapse_slice_from_janus_gauge_probe import (
    build_payload as build_lapse_slice,
)
from scripts.build_p0_phi_j_l_boundary_selector_probe import (
    build_payload as build_boundary_selector,
)
from scripts.build_p0_phi_j_l_intrinsic_selector_attempt import (
    build_payload as build_intrinsic_selector,
)
from scripts.build_p0_phi_j_l_underselection_probe import (
    build_payload as build_underselection,
)


REPORT_PATH = Path("outputs/reports/p0_phi_j_l_remaining_lock_decision_matrix.md")
JSON_PATH = Path("outputs/reports/p0_phi_j_l_remaining_lock_decision_matrix.json")


def build_payload() -> dict:
    underselection = build_underselection()
    janus_selector = build_janus_selector()
    b4vol_degeneracy = build_b4vol_degeneracy()
    lapse_slice = build_lapse_slice()
    intrinsic = build_intrinsic_selector()
    boundary = build_boundary_selector()

    rows = [
        {
            "route": "m15_m30_only_general_perturbed",
            "source_basis": "published coupled field/source weights",
            "selects_unique_phi_j_l": False,
            "source_derived": True,
            "scope": "general perturbed branch",
            "status": "blocked",
            "reason": (
                "source weights fix B4vol, but B4vol=J_phi*lapse_slice_ratio "
                "does not determine J_phi without a selected lapse/slice/gauge"
            ),
        },
        {
            "route": "flrw_comoving_conditional",
            "source_basis": "FLRW/comoving ansatz plus proper-time slicing",
            "selects_unique_phi_j_l": True,
            "source_derived": False,
            "scope": "restricted background branch only",
            "status": "conditional",
            "reason": (
                "the ansatz can fix lapse/slice, but this is not a proof for "
                "general non-comoving or perturbed transport"
            ),
        },
        {
            "route": "intrinsic_minimal_distortion",
            "source_basis": "no-fit variational selector",
            "selects_unique_phi_j_l": bool(intrinsic["intrinsic_selector_fixes_toy_family"]),
            "source_derived": bool(intrinsic["source_derived_from_janus"]),
            "scope": "toy family, candidate research principle",
            "status": "new-principle",
            "reason": "selects the toy family but is not derived from Janus source equations",
        },
        {
            "route": "strong_boundary_or_gauge_selector",
            "source_basis": "extra pointwise boundary/gauge condition",
            "selects_unique_phi_j_l": bool(boundary["strong_selectors_exist"]),
            "source_derived": bool(boundary["strong_selectors_source_supplied"]),
            "scope": "toy family, boundary-selected",
            "status": "new-boundary-axiom",
            "reason": "can fix epsilon, but the condition is not supplied by the Janus sources",
        },
        {
            "route": "full_phi_or_scouple_action",
            "source_basis": "missing covariant action/source selection",
            "selects_unique_phi_j_l": False,
            "source_derived": False,
            "scope": "would cover general branch if found",
            "status": "not-supplied",
            "reason": "no accepted source action in the current artifact chain selects phi/J/L",
        },
    ]
    return {
        "description": (
            "Decision matrix for the remaining P0 phi/J/L lock after local "
            "integrability, B4vol and D L identities are available."
        ),
        "status": "phi-j-l-remaining-lock-open",
        "rows": rows,
        "underselection_probe_available": True,
        "underselection_proved_for_family": bool(
            underselection["underselection_proved_for_family"]
        ),
        "b4vol_jacobian_gauge_degeneracy_proved": bool(
            b4vol_degeneracy["degeneracy_symbolic_identity_closed"]
        ),
        "source_b4vol_alone_selects_jphi": bool(
            b4vol_degeneracy["source_b4vol_alone_selects_jphi"]
        ),
        "requires_slice_lapse_selector": bool(
            b4vol_degeneracy["requires_slice_lapse_selector"]
        ),
        "janus_equations_select_b4vol_weight": bool(
            janus_selector["janus_equations_select_b4vol_weight"]
        ),
        "janus_equations_select_phi_without_extra_gauge": bool(
            janus_selector["janus_equations_select_phi_without_extra_gauge"]
        ),
        "general_perturbed_branch_lapse_slice_fixed": bool(
            lapse_slice["general_perturbed_branch_lapse_slice_fixed"]
        ),
        "proper_time_slicing_can_fix_lapse": bool(lapse_slice["proper_time_slicing_can_fix_lapse"]),
        "flrw_comoving_branch_can_fix_lapse_slice": bool(
            lapse_slice["flrw_comoving_branch_can_fix_lapse_slice"]
        ),
        "m15_m30_only_bounded_no_go_for_general_selector": True,
        "clean_general_route_without_new_axiom_found": False,
        "clean_conditional_flrw_route_available": True,
        "clean_candidate_new_principles_available": True,
        "new_axiom_required_for_general_perturbed_selection": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "recommended_next_steps": [
            "keep the FLRW/comoving branch explicitly conditional",
            "try to derive a covariant selector from the Janus action/source terms",
            "if adopting minimal distortion, label it as a new axiom before simulations",
            "do not promote Q_det, Q_cross or a fitted normalization into phi/J selection",
        ],
        "verdict": (
            "The clean bounded conclusion is negative for the general branch: "
            "M15/M30-style source weights select B4vol but not a unique phi/J/L. "
            "A general closure needs either a source-derived selector or an explicit "
            "new axiom; the FLRW/comoving path remains conditional only."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phi/J/L Remaining Lock Decision Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Underselection proved for family: {payload['underselection_proved_for_family']}",
        (
            "B4vol/Jacobian gauge degeneracy proved: "
            f"{payload['b4vol_jacobian_gauge_degeneracy_proved']}"
        ),
        f"Source B4vol alone selects J_phi: {payload['source_b4vol_alone_selects_jphi']}",
        f"Requires slice/lapse selector: {payload['requires_slice_lapse_selector']}",
        f"Janus equations select B4vol weight: {payload['janus_equations_select_b4vol_weight']}",
        (
            "Janus equations select phi without extra gauge: "
            f"{payload['janus_equations_select_phi_without_extra_gauge']}"
        ),
        (
            "General perturbed branch lapse/slice fixed: "
            f"{payload['general_perturbed_branch_lapse_slice_fixed']}"
        ),
        (
            "M15/M30-only bounded no-go for general selector: "
            f"{payload['m15_m30_only_bounded_no_go_for_general_selector']}"
        ),
        (
            "Clean general route without new axiom found: "
            f"{payload['clean_general_route_without_new_axiom_found']}"
        ),
        f"Clean conditional FLRW route available: {payload['clean_conditional_flrw_route_available']}",
        (
            "Clean candidate new principles available: "
            f"{payload['clean_candidate_new_principles_available']}"
        ),
        (
            "New axiom required for general perturbed selection: "
            f"{payload['new_axiom_required_for_general_perturbed_selection']}"
        ),
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Routes",
        "",
        "| route | source basis | selects unique phi/J/L | source derived | scope | status |",
        "|---|---|---:|---:|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['route']} | {row['source_basis']} | "
            f"{row['selects_unique_phi_j_l']} | {row['source_derived']} | "
            f"{row['scope']} | {row['status']} |"
        )
    lines.extend(["", "## Reasons", ""])
    for row in payload["rows"]:
        lines.append(f"- `{row['route']}`: {row['reason']}")
    lines.extend(["", "## Recommended Next Steps", ""])
    lines.extend(f"- {item}" for item in payload["recommended_next_steps"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

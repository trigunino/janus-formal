from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_scouple_accepted_action_search import (
    build_payload as build_accepted_action_search,
)
from scripts.build_p0_external_source_search_scouple_phi_audit import (
    build_payload as build_external_scouple_audit,
)
from scripts.build_p0_janus_weak_selector_action_origin_audit import (
    build_payload as build_weak_selector_origin,
)


REPORT_PATH = Path("outputs/reports/p0_janus_active_cross_action_acceptance_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_active_cross_action_acceptance_gate.json")


def build_payload() -> dict:
    accepted = build_accepted_action_search()
    external = build_external_scouple_audit()
    origin = build_weak_selector_origin()
    source_material = {
        "M15_source_card_exists": Path("docs/source_cards/M15.md").exists(),
        "M30_source_card_exists": Path("docs/source_cards/M30.md").exists(),
        "M15_local_text_extract_exists": bool(list(Path("data").glob("**/M15*.txt"))),
        "M30_local_text_extract_exists": bool(list(Path("data").glob("**/M30*.txt"))),
        "M15_local_pdf_exists": bool(list(Path("data").glob("**/M15*.pdf"))),
        "M30_local_pdf_exists": bool(list(Path("data").glob("**/M30*.pdf"))),
    }
    acceptance_rows = [
        {
            "check": "field_equation_source_slot",
            "required": "Janus equations contain determinant-weighted cross stress in receiver field equation",
            "available": bool(accepted["m15_action_accepted_for_field_equations"]),
            "accepts_active_action": False,
        },
        {
            "check": "independent_scouple",
            "required": "source supplies independent S_x/S_couple varied with respect to phi/L",
            "available": bool(accepted["independent_scouple_found"]),
            "accepts_active_action": False,
        },
        {
            "check": "map_variation",
            "required": "source derives delta_phi S_x = -int xi div T_to_self",
            "available": bool(external["explicit_variational_transport_law_found"]),
            "accepts_active_action": False,
        },
        {
            "check": "weak_selector_shape",
            "required": "candidate active S_x mathematically derives h div T = rho h Cuu",
            "available": bool(origin["weak_selector_derivation_shape_closed"]),
            "accepts_active_action": "math-shape-only",
        },
        {
            "check": "no_rustine",
            "required": "no multiplier, no Qdet/Qcross absorption, no observational fit",
            "available": bool(
                origin["multiplier_route_rejected_as_rustine"]
                and not origin["requires_observational_fit"]
                and not origin["uses_qdet_qcross_absorption"]
            ),
            "accepts_active_action": True,
        },
    ]
    blockers = [
        "M15 supplies a bivariational total action for field equations, not an independent active S_x varied in phi/L",
        "external audit found coupled field equations but no explicit variational transport law for phi/L",
        "the active cross action is mathematically adequate but not source-accepted as published Janus",
        "adopting it would be a declared new Janus-compatible axiom, not a recovered published equation",
    ]
    return {
        "description": "Acceptance gate for the active receiver-coupled cross-dust action.",
        "status": "active-cross-action-math-valid-source-not-accepted",
        "acceptance_rows": acceptance_rows,
        "blockers": blockers,
        "source_material": source_material,
        "source_material_sufficient_for_reaudit": bool(
            source_material["M15_local_text_extract_exists"]
            or source_material["M15_local_pdf_exists"]
        ),
        "m15_field_equation_action_available": bool(accepted["m15_action_accepted_for_field_equations"]),
        "m15_accepted_as_scouple": bool(accepted["m15_action_accepted_as_scouple"]),
        "independent_scouple_found": bool(accepted["independent_scouple_found"]),
        "external_variational_transport_law_found": bool(
            external["explicit_variational_transport_law_found"]
        ),
        "active_cross_action_derives_weak_selector": bool(
            origin["active_cross_dust_action_derives_weak_selector"]
        ),
        "active_cross_action_source_accepted": False,
        "can_adopt_as_published_janus": False,
        "can_adopt_as_explicit_new_axiom": True,
        "new_axiom_adopted": False,
        "requires_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The active cross action is a valid mathematical completion for the weak selector, "
            "but current Janus source audits do not accept it as a published phi/L variational law. "
            "It must remain a proposed new axiom unless a source-derived S_x is found."
        ),
        "next_research_step": (
            "acquire_or_restore_M15_M30_raw_sources_then_reaudit_S_cross"
            if not (
                source_material["M15_local_text_extract_exists"]
                or source_material["M15_local_pdf_exists"]
            )
            else "reopen_M15_M30_S_cross_phi_L_source_audit"
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Active Cross Action Acceptance Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"M15 field-equation action available: {payload['m15_field_equation_action_available']}",
        f"M15 accepted as S_couple: {payload['m15_accepted_as_scouple']}",
        f"Independent S_couple found: {payload['independent_scouple_found']}",
        f"External variational transport law found: {payload['external_variational_transport_law_found']}",
        f"Active cross action derives weak selector: {payload['active_cross_action_derives_weak_selector']}",
        f"Active cross action source accepted: {payload['active_cross_action_source_accepted']}",
        f"Source material sufficient for reaudit: {payload['source_material_sufficient_for_reaudit']}",
        f"Can adopt as published Janus: {payload['can_adopt_as_published_janus']}",
        f"Can adopt as explicit new axiom: {payload['can_adopt_as_explicit_new_axiom']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Requires observational fit: {payload['requires_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Acceptance Rows",
        "",
        "| check | required | available | accepts active action |",
        "|---|---|---:|---:|",
    ]
    for row in payload["acceptance_rows"]:
        lines.append(
            f"| {row['check']} | {row['required']} | {row['available']} | "
            f"{row['accepts_active_action']} |"
        )
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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

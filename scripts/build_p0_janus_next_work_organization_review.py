from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_active_cross_action_acceptance_gate import (
    build_payload as build_active_cross_acceptance,
)
from scripts.build_p0_janus_source_isometry_selection_no_go import (
    build_payload as build_isometry_no_go,
)
from scripts.build_p0_janus_pulled_dust_action_weak_congruence_proof import (
    build_payload as build_weak_dust_proof,
)
from scripts.build_p0_source_derived_closure_checklist import (
    build_payload as build_source_checklist,
)


REPORT_PATH = Path("outputs/reports/p0_janus_next_work_organization_review.md")
JSON_PATH = Path("outputs/reports/p0_janus_next_work_organization_review.json")


def build_payload() -> dict:
    active = build_active_cross_acceptance()
    isometry = build_isometry_no_go()
    weak_dust = build_weak_dust_proof()
    checklist = build_source_checklist()
    layers = [
        {
            "layer": "sources",
            "purpose": "published Janus equations, PDFs, source traceability",
            "use_for": "decide whether a law is Janus-published or a new axiom",
        },
        {
            "layer": "math_gates",
            "purpose": "theorems, no-go results, formal variation targets",
            "use_for": "avoid reusing false routes such as generic metric isometry",
        },
        {
            "layer": "conditional_branches",
            "purpose": "dust weak congruence, L_solder special branch, diagnostics",
            "use_for": "run controlled tests without claiming prediction",
        },
        {
            "layer": "simulation",
            "purpose": "PM/Vlasov/lensing probes",
            "use_for": "numerical diagnostics after physical closure gates are satisfied",
        },
    ]
    missing_core = [
        {
            "missing": "source-accepted S_x/S_couple or phi/L transport law",
            "why_it_matters": "selects phi/L and derives weak selector instead of imposing it",
            "current_state": "math-valid active cross action exists, but source not accepted",
        },
        {
            "missing": "mirror plus/minus proof",
            "why_it_matters": "prevents two independent map/gauge choices",
            "current_state": "inverse-map algebra exists; action/source mirror not closed",
        },
        {
            "missing": "same-L/DL law",
            "why_it_matters": "one L must serve K, Q_cross, Vlasov and Bianchi residuals",
            "current_state": "same-L algebra exists; source-derived dynamic law open",
        },
        {
            "missing": "B4vol lapse/slice/J branch",
            "why_it_matters": "fixes measure terms without Q_det double counting",
            "current_state": "single dust pullback works; general perturbed branch open",
        },
        {
            "missing": "non-dust matter closure",
            "why_it_matters": "pressure, EOS, Pi and Vlasov moments are needed beyond dust",
            "current_state": "dust branch conditional; pressure/Pi remain blocked",
        },
    ]
    decision_tree = [
        {
            "route": "find_source",
            "action": "search/derive a published Janus variational phi/L law",
            "if_success": "upgrade active cross action acceptance and mirror proof",
            "if_fail": "do not claim published closure",
        },
        {
            "route": "new_axiom",
            "action": "declare active cross action as explicit Janus-compatible axiom",
            "if_success": "test split Noether, mirror, stability, pressure/Pi",
            "if_fail": "keep prediction blocked",
        },
        {
            "route": "no_new_axiom",
            "action": "continue integrability/no-go/kinetic-sheet routes",
            "if_success": "force a map without new S_x",
            "if_fail": "prove a new principle is unavoidable",
        },
    ]
    recommended_next = [
        "finish mirror proof for the weak selector under the active cross action candidate",
        "write the active cross action as an explicit optional axiom, but keep new_axiom_adopted=False",
        "run split Noether/stability acceptance on that candidate",
        "only then decide whether to adopt the axiom or keep searching source-derived routes",
    ]
    return {
        "description": "Compact organization review for continuing the Janus P0 program.",
        "status": "organized-next-work-index-ready",
        "layers": layers,
        "missing_core": missing_core,
        "decision_tree": decision_tree,
        "recommended_next": recommended_next,
        "key_artifacts": [
            "p0_janus_active_cross_action_acceptance_gate",
            "p0_janus_weak_selector_action_origin_audit",
        "p0_janus_pulled_dust_action_weak_congruence_proof",
        "p0_janus_source_isometry_selection_no_go",
        "p0_no_axiom_route_exhaustion_program",
        "p0_source_derived_closure_checklist",
        ],
        "active_cross_action_math_valid": bool(active["active_cross_action_derives_weak_selector"]),
        "active_cross_action_source_accepted": bool(active["active_cross_action_source_accepted"]),
        "no_axiom_exhaustion_program_available": True,
        "generic_metric_isometry_rejected": bool(isometry["pure_l_solder_generic_route_rejected"]),
        "weak_dust_target_reached": bool(weak_dust["projected_cuu_target_reached"]),
        "all_source_items_derived": bool(checklist["all_items_source_derived"]),
        "new_axiom_adopted": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "What is missing is not more numerical tooling; it is a source-accepted "
            "interaction/transport law selecting phi/L. The best practical organization is "
            "to keep sources, math gates, conditional branches and simulations separate, then "
            "advance the active cross action through mirror/Noether/stability as an optional "
            "axiom while continuing source-derived searches."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Next Work Organization Review",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Active cross action math valid: {payload['active_cross_action_math_valid']}",
        f"Active cross action source accepted: {payload['active_cross_action_source_accepted']}",
        f"No-axiom exhaustion program available: {payload['no_axiom_exhaustion_program_available']}",
        f"Generic metric isometry rejected: {payload['generic_metric_isometry_rejected']}",
        f"Weak dust target reached: {payload['weak_dust_target_reached']}",
        f"All source items derived: {payload['all_source_items_derived']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Organization Layers",
        "",
        "| layer | purpose | use for |",
        "|---|---|---|",
    ]
    for row in payload["layers"]:
        lines.append(f"| {row['layer']} | {row['purpose']} | {row['use_for']} |")
    lines.extend(["", "## Missing Core", "", "| missing | why it matters | current state |", "|---|---|---|"])
    for row in payload["missing_core"]:
        lines.append(
            f"| {row['missing']} | {row['why_it_matters']} | {row['current_state']} |"
        )
    lines.extend(["", "## Decision Tree", "", "| route | action | success | fail |", "|---|---|---|---|"])
    for row in payload["decision_tree"]:
        lines.append(f"| {row['route']} | {row['action']} | {row['if_success']} | {row['if_fail']} |")
    lines.extend(["", "## Recommended Next", ""])
    lines.extend(f"- {item}" for item in payload["recommended_next"])
    lines.extend(["", "## Key Artifacts", ""])
    lines.extend(f"- `{item}`" for item in payload["key_artifacts"])
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

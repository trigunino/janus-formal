from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_holonomy_loop_consistency_criteria import build_payload as build_holonomy
from scripts.build_p0_route_c_small_loop_holonomy_numeric_probe import (
    build_payload as build_small_loop,
)
from scripts.build_p0_route_c_two_path_nonunique_l_probe import (
    build_payload as build_two_path,
)
from scripts.build_p0_same_l_bridge_induces_m_k_qcross_gate import build_payload as build_same_l
from scripts.build_p0_weakfield_relative_curvature_rows_target import build_payload as build_weakfield


REPORT_PATH = Path("outputs/reports/p0_route_c_phi_r_relative_curvature_selector_probe.md")
JSON_PATH = Path("outputs/reports/p0_route_c_phi_r_relative_curvature_selector_probe.json")


def build_payload() -> dict:
    weakfield = build_weakfield()
    same_l = build_same_l()
    holonomy = build_holonomy()
    small_loop = build_small_loop()
    two_path = build_two_path()
    probe_rows = [
        {
            "probe": "phi_r_source_candidate",
            "formula": "Phi_R_candidate := Delta_R[Delta_Phi, Delta_Psi]",
            "accepted": bool(weakfield["source_curvature_rows_computable"]),
            "closed": False,
        },
        {
            "probe": "curvature_match_residual",
            "formula": "||F_Omega - Phi_R_candidate||_eta < tol",
            "accepted": False,
            "closed": False,
        },
        {
            "probe": "small_loop_holonomy_residual",
            "formula": "Hol_loop(Omega) - I - area * Phi_R_candidate = O(area^2)",
            "accepted": False,
            "closed": False,
        },
        {
            "probe": "segmentation_invariance",
            "formula": "transport(path) = transport(subdivided path)",
            "accepted": False,
            "closed": False,
        },
        {
            "probe": "same_l_k_qcross_residual",
            "formula": "same L induces K[L], Q_cross[L], and Vlasov moments",
            "accepted": bool(same_l["same_l_stack_algebra_closed"]),
            "closed": False,
        },
    ]
    negative_controls = [
        {
            "control": "curl_defected_phi_r",
            "expected": "reject",
            "reason": "relative curvature rows must satisfy the declared Bianchi/curl consistency test",
            "rejected": True,
        },
        {
            "control": "independent_optical_l",
            "expected": "reject",
            "reason": "Q_cross cannot use a different L than K and kinetic transport",
            "rejected": True,
        },
        {
            "control": "qdet_qcross_absorption",
            "expected": "reject",
            "reason": "scalar factors cannot absorb missing curvature, holonomy, or tensor transport residuals",
            "rejected": True,
        },
    ]
    return {
        "description": (
            "Route C weak-field selector probe: replace free Phi_R by the "
            "source-computable relative curvature rows Delta_R[Delta_Phi, Delta_Psi], "
            "then require curvature, small-loop holonomy, segmentation, and same-L "
            "tests before any prediction."
        ),
        "status": "phi-r-relative-curvature-selector-probe-open",
        "depends_on": [
            "p0_bf_connection_constraint_route",
            "p0_route_c_bf_holonomy_priority_attack",
            "p0_weakfield_relative_curvature_rows_target",
            "p0_same_l_bridge_induces_m_k_qcross_gate",
            "p0_holonomy_loop_consistency_criteria",
        ],
        "weakfield_status": weakfield["status"],
        "holonomy_status": holonomy["status"],
        "same_l_status": same_l["status"],
        "small_loop_holonomy_status": small_loop["status"],
        "two_path_nonunique_l_status": two_path["status"],
        "phi_r_source_candidate": "weakfield_relative_curvature_rows",
        "probe_rows": probe_rows,
        "negative_controls": negative_controls,
        "phi_r_free_insert_allowed": False,
        "curl_defected_phi_r_rejected": True,
        "independent_optical_l_rejected": True,
        "qdet_qcross_absorption_rejected": True,
        "small_loop_holonomy_numeric_probe_available": True,
        "small_loop_constant_curvature_closes": bool(
            small_loop["constant_curvature_holonomy_first_order_closes"]
        ),
        "small_loop_segmentation_closes": bool(
            small_loop["constant_curvature_segmentation_closes"]
        ),
        "noncommuting_path_order_changes_holonomy": bool(
            small_loop["noncommuting_path_order_changes_holonomy"]
        ),
        "two_path_nonunique_l_probe_available": True,
        "two_paths_select_different_l": bool(two_path["two_paths_select_different_l"]),
        "path_rule_required_for_unique_l": bool(two_path["path_rule_required_for_unique_l"]),
        "l_selected_conditionally": True,
        "l_uniquely_selected": False,
        "weakfield_only": True,
        "path_rule_source_derived": bool(holonomy["source_derived"]),
        "same_l_stack_algebra_closed": bool(same_l["same_l_stack_algebra_closed"]),
        "same_l_transport_source_closed": bool(same_l["l_source_selected"]),
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is a real narrowing of Route C: Phi_R is tested as a Janus "
            "weak-field relative curvature candidate instead of a free BF target. "
            "It remains non-predictive because L is only conditionally selected, "
            "the path rule is not source-derived, and same-L transport is not "
            "source-closed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Phi_R Relative Curvature Selector Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Phi_R source candidate: `{payload['phi_r_source_candidate']}`",
        f"Phi_R free insert allowed: {payload['phi_r_free_insert_allowed']}",
        f"L selected conditionally: {payload['l_selected_conditionally']}",
        f"L uniquely selected: {payload['l_uniquely_selected']}",
        f"Weakfield only: {payload['weakfield_only']}",
        f"Path rule source derived: {payload['path_rule_source_derived']}",
        f"Same-L stack algebra closed: {payload['same_l_stack_algebra_closed']}",
        f"Same-L transport source closed: {payload['same_l_transport_source_closed']}",
        f"Small-loop holonomy numeric probe available: {payload['small_loop_holonomy_numeric_probe_available']}",
        f"Small-loop constant curvature closes: {payload['small_loop_constant_curvature_closes']}",
        f"Small-loop segmentation closes: {payload['small_loop_segmentation_closes']}",
        f"Noncommuting path order changes holonomy: {payload['noncommuting_path_order_changes_holonomy']}",
        f"Two-path nonunique L probe available: {payload['two_path_nonunique_l_probe_available']}",
        f"Two paths select different L: {payload['two_paths_select_different_l']}",
        f"Path rule required for unique L: {payload['path_rule_required_for_unique_l']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Probes",
        "",
        "| probe | formula | accepted | closed |",
        "|---|---|---:|---:|",
    ]
    for row in payload["probe_rows"]:
        lines.append(f"| {row['probe']} | `{row['formula']}` | {row['accepted']} | {row['closed']} |")
    lines.extend(["", "## Negative Controls", "", "| control | expected | reason | rejected |", "|---|---|---|---:|"])
    for row in payload["negative_controls"]:
        lines.append(f"| {row['control']} | {row['expected']} | {row['reason']} | {row['rejected']} |")
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

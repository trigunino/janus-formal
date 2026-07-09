from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_alpha_selection_route_coverage_audit.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_alpha_selection_route_coverage_audit.md"

ROUTE_REPORTS = {
    1: "p0_eft_janus_z2_global_action_onshell_alpha_selector_gate.json",
    2: "p0_eft_janus_z2_alpha_two_hard_routes_gate.json",
    3: "p0_eft_janus_z2_null_pt_thermodynamic_alpha_selector_gate.json",
    4: "p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate.json",
    5: "p0_eft_janus_z2_sigma_torsion_source_exhaustion_gate.json",
    6: "p0_eft_janus_z2_alpha_composite_selector_frontier_gate.json",
    7: "p0_eft_janus_z2_bimetric_vacuum_alpha_selector_gate.json",
    8: "p0_eft_janus_z2_sigma_boundary_projection_from_theta_pt67_gate.json",
    9: "p0_eft_janus_z2_observational_alpha_sector_policy_gate.json",
    10: "p0_eft_janus_z2_moebius_twisted_cycle_alpha_route_gate.json",
    11: "p0_eft_janus_z2_moebius_twisted_cycle_alpha_route_gate.json",
    12: "p0_eft_janus_z2_primitive_sector_n_selection_gate.json",
}


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _route_status(route_id: int, payload: dict) -> str:
    if not payload:
        return "missing_report"
    if payload.get("no_fit_prediction") is False:
        return "observational_not_no_fit"
    if payload.get("alpha_selector_ready") is True:
        return "selector_ready"
    if payload.get("archive_torsionful_branch_recommended") is True:
        return "archive_ready"
    if payload.get("state_sector_closure_blocked") is True:
        return "state_sector_closure_blocked"
    if payload.get("chi_LL_derivation_ready") is False:
        return "evaluated_blocked_or_conditional"
    if payload.get("gate_passed") is True:
        return "evaluated_blocked_or_conditional"
    return "report_present_unclassified"


def build_payload() -> dict:
    route_rows = []
    for route_id, filename in ROUTE_REPORTS.items():
        path = REPORTS / filename
        payload = _read(path)
        route_rows.append(
            {
                "id": route_id,
                "report": str(path),
                "report_exists": path.exists(),
                "coverage_status": _route_status(route_id, payload),
            }
        )

    missing = [r["id"] for r in route_rows if r["coverage_status"] == "missing_report"]
    selectors = [r["id"] for r in route_rows if r["coverage_status"] == "selector_ready"]
    return {
        "status": "janus-z2-alpha-selection-route-coverage-audit",
        "active_core": "Z2_tunnel_Sigma",
        "route_count": len(route_rows),
        "routes": route_rows,
        "missing_route_ids": missing,
        "no_fit_selector_ready_route_ids": selectors,
        "all_routes_have_reports": len(missing) == 0,
        "alpha_no_fit_selector_found": len(selectors) > 0,
        "next_uncovered_or_weak_routes": missing,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha Selection Route Coverage Audit",
        "",
        f"All routes have reports: `{payload['all_routes_have_reports']}`",
        f"No-fit selector found: `{payload['alpha_no_fit_selector_found']}`",
        f"Missing route ids: `{payload['missing_route_ids']}`",
        "",
        "## Routes",
    ]
    for row in payload["routes"]:
        lines.append(
            f"- {row['id']}: `{row['coverage_status']}` ({row['report_exists']})"
        )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_lgeom_dl_lie_residual_probe import build_payload as build_dl_probe
from scripts.build_p0_janus_lgeom_tetrad_map_residual_probe import build_payload as build_lgeom_probe
from scripts.build_p0_janus_metric_force_vlasov_step_probe import build_payload as build_vlasov_step_probe
from scripts.build_p0_janus_two_sector_metric_force_vlasov_probe import (
    build_payload as build_two_sector_vlasov_probe,
)
from scripts.build_p0_janus_weakfield_b4vol_product_rule_probe import (
    build_payload as build_b4vol_probe,
)
from scripts.build_p0_janus_weakfield_metric_force_probe import build_payload as build_metric_probe


REPORT_PATH = Path("outputs/reports/p0_janus_diagnostic_closure_dashboard.md")
JSON_PATH = Path("outputs/reports/p0_janus_diagnostic_closure_dashboard.json")


PROBE_BUILDERS = [
    ("p0_janus_lgeom_tetrad_map_residual_probe", build_lgeom_probe),
    ("p0_janus_lgeom_dl_lie_residual_probe", build_dl_probe),
    ("p0_janus_weakfield_b4vol_product_rule_probe", build_b4vol_probe),
    ("p0_janus_weakfield_metric_force_probe", build_metric_probe),
    ("p0_janus_metric_force_vlasov_step_probe", build_vlasov_step_probe),
    ("p0_janus_two_sector_metric_force_vlasov_probe", build_two_sector_vlasov_probe),
]

PROBE_BLOCKERS = {
    "p0_janus_lgeom_tetrad_map_residual_probe": [
        "raw L_geom is Lorentz only on equal-tetrad diagnostics",
        "same-L branch is not source-selected",
    ],
    "p0_janus_lgeom_dl_lie_residual_probe": [
        "D L Lie-algebra obstruction remains outside equal branch",
        "D L law is not derived from Janus sources",
    ],
    "p0_janus_weakfield_b4vol_product_rule_probe": [
        "1+1 B4vol product rule is not the 4D source measure",
        "Q_det convention is not closed",
    ],
    "p0_janus_weakfield_metric_force_probe": [
        "metric/tetrad branch is not source-selected",
        "B4vol remains diagnostic",
    ],
    "p0_janus_metric_force_vlasov_step_probe": [
        "phase-space transport is not source-selected",
        "same-L transport is absent",
    ],
    "p0_janus_two_sector_metric_force_vlasov_probe": [
        "two-sector metric-force chain is diagnostic only",
        "R_plus/R_minus and same-L closure are not proved",
    ],
}


def _row(name: str, payload: dict) -> dict:
    return {
        "probe": name,
        "status": payload["status"],
        "diagnostic_only": bool(payload.get("diagnostic_only", False)),
        "physics_closed": bool(payload.get("physics_closed", False)),
        "prediction_ready": bool(payload.get("prediction_ready", False)),
        "open_blockers": PROBE_BLOCKERS[name],
        "boundary": payload.get("boundary", ""),
    }


def build_payload(consume_graph: bool = True) -> dict:
    probe_rows = [_row(name, builder()) for name, builder in PROBE_BUILDERS]
    if consume_graph:
        from scripts.build_p0_blocker_dependency_graph import build_payload as build_blocker_graph

        graph_payload = build_blocker_graph()
        graph_rows = {row["blocker"]: row for row in graph_payload["blockers"]}
        graph_available_flags = {
            key: value for key, value in graph_payload.items() if key.endswith("_available")
        }
    else:
        graph_payload = {
            "all_blockers_closed": False,
            "open_blockers": [],
            "source_residual_matrix_status": "not-consumed",
            "janus_source_residual_closure_obligation_matrix_available": True,
            "physics_closed": False,
            "prediction_ready": False,
        }
        graph_rows = {
            "D L transport law": {"closed": False},
            "D log B_4vol measure law": {"closed": False},
            "source-measure branch selection": {"closed": False},
        }
        graph_available_flags = {}
    blocking_findings = [
        "raw L_geom is rejected outside equal-tetrad branches",
        "D L/Lie-algebra residual is computed but not source-derived from Janus",
        "B4vol product-rule check is 1+1 diagnostic, not the 4D Janus source law",
        "metric-force/Vlasov chain is diagnostic and not a source-selected Janus branch",
        "same L, same Omega, mirror inverse, DlogB, R_plus/R_minus remain open",
        "source residual closure obligation matrix must be satisfied before closure",
        "Q_det/Q_cross absorption is forbidden as scalar closure",
    ]
    payload = {
        "description": "P0 diagnostic closure dashboard for weak-field L, B4vol, metric-force and Vlasov probes.",
        "status": (
            "diagnostic-closure-dashboard-closed"
            if graph_payload["all_blockers_closed"]
            else "diagnostic-closure-dashboard-open"
        ),
        "blocker_graph_consumed": True,
        "graph_open_blockers": graph_payload["open_blockers"],
        "graph_all_blockers_closed": bool(graph_payload["all_blockers_closed"]),
        "source_residual_matrix_status": graph_payload["source_residual_matrix_status"],
        "probe_rows": probe_rows,
        "blocking_findings": blocking_findings,
        "all_probe_reports_non_predictive": all(not row["prediction_ready"] for row in probe_rows),
        "all_probe_reports_diagnostic": all(row["diagnostic_only"] for row in probe_rows),
        "raw_lgeom_promoted": False,
        "dl_source_derived": bool(graph_rows["D L transport law"]["closed"]),
        "b4vol_source_law_derived": bool(graph_rows["D log B_4vol measure law"]["closed"]),
        "source_selected_metric_branch": bool(graph_rows["source-measure branch selection"]["closed"]),
        "same_l_transport_closed": bool(graph_rows["D L transport law"]["closed"]),
        "effective_vlasov_solver_physics_ready": False,
        "source_residual_closure_obligation_matrix_available": bool(
            graph_payload["janus_source_residual_closure_obligation_matrix_available"]
        ),
        "uses_observational_fit": False,
        "physics_closed": bool(graph_payload["physics_closed"]),
        "prediction_ready": bool(graph_payload["prediction_ready"]),
        "verdict": (
            "The probes narrow the failure surface but do not close Janus physics. "
            "Next proof must source-derive metric/tetrad, same-L/DL, B4vol law and residual closure "
            "without Q_det/Q_cross absorption."
        ),
    }
    payload.update(graph_available_flags)
    return payload


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Diagnostic Closure Dashboard",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All probe reports non-predictive: {payload['all_probe_reports_non_predictive']}",
        f"All probe reports diagnostic: {payload['all_probe_reports_diagnostic']}",
        f"Raw Lgeom promoted: {payload['raw_lgeom_promoted']}",
        f"D L source-derived: {payload['dl_source_derived']}",
        f"B4vol source law derived: {payload['b4vol_source_law_derived']}",
        f"Source-selected metric branch: {payload['source_selected_metric_branch']}",
        f"Same-L transport closed: {payload['same_l_transport_closed']}",
        f"Effective Vlasov solver physics ready: {payload['effective_vlasov_solver_physics_ready']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Probes",
        "",
        "| probe | status | diagnostic | physics_closed | prediction_ready |",
        "|---|---|---:|---:|---:|",
    ]
    for row in payload["probe_rows"]:
        lines.append(
            f"| {row['probe']} | {row['status']} | {row['diagnostic_only']} | "
            f"{row['physics_closed']} | {row['prediction_ready']} |"
        )
    lines.extend(["", "## Per-Probe Open Blockers", ""])
    for row in payload["probe_rows"]:
        lines.append(f"- {row['probe']}: {'; '.join(row['open_blockers'])}")
    lines.extend(["", "## Blocking Findings", ""])
    lines.extend(f"- {item}" for item in payload["blocking_findings"])
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

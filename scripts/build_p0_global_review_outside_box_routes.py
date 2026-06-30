from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_global_review_outside_box_routes.md")
JSON_PATH = Path("outputs/reports/p0_global_review_outside_box_routes.json")


def build_payload() -> dict:
    closed_work = [
        "M15/M30 determinant cross-source anchor for B_4vol",
        "single pulled cross-dust effective continuity",
        "single declared phi/L dust bridge hE=rho hCuu",
        "inverse-map mirror consistency when imposed in the action",
        "anti-rustine gate showing Phi/S_couple is not source-forced",
    ]
    open_blockers = [
        {
            "blocker": "dynamic_phi_l_selection",
            "state": "not source-derived; requires new source or explicit new axiom",
            "severity": "P0",
        },
        {
            "blocker": "full_bianchi_residuals",
            "state": "R_plus/R_minus not closed without accepted K/Phi/S_couple",
            "severity": "P0",
        },
        {
            "blocker": "non_dust_matter",
            "state": "pressure, projector transport, Pi and T0i remain open",
            "severity": "P0",
        },
        {
            "blocker": "observable_chain",
            "state": "IC, Weyl/shear/distance and survey likelihood not prediction-ready",
            "severity": "P1",
        },
    ]
    outside_box_routes = [
        {
            "route": "integrability-first",
            "idea": "derive phi/L from Frobenius/curl-free dust-image conditions instead of adding S_couple",
            "classification": "source-compatible search",
            "acceptance": "unique map from dust congruence plus mirror; no free functions",
            "risk": "may fail after caustics or multistreaming",
        },
        {
            "route": "optimal-transport-map",
            "idea": "choose phi as the unique mass-measure transport minimizing a Janus geometric cost",
            "classification": "new-principle candidate",
            "acceptance": "cost fixed by metrics only and recovers B_4vol/geodesic signs",
            "risk": "new axiom unless the cost is sourced from Janus",
        },
        {
            "route": "BF-or-connection-constraint",
            "idea": "treat L as a solder/connection field constrained by flatness or relative holonomy",
            "classification": "geometric completion candidate",
            "acceptance": "derives F_alpha and same-L Q_cross/K transport with no fit",
            "risk": "may overconstrain generic bimetric curvature",
        },
        {
            "route": "kinetic-sheet-limit",
            "idea": "avoid single-fluid phi by summing sheetwise dust pullbacks through phase-space transport",
            "classification": "simulation-compatible diagnostic route",
            "acceptance": "sheet sum conserves B_4vol current and produces Q_cross from velocities",
            "risk": "not a tensor proof until continuum limit and stress closure are derived",
        },
        {
            "route": "no-go theorem",
            "idea": "prove no local low-derivative Phi can satisfy all constraints, forcing a nonlocal or kinetic completion",
            "classification": "falsification/selection route",
            "acceptance": "excludes the current invariant family, not just examples",
            "risk": "hard proof; may only narrow the family",
        },
    ]
    next_experiments = [
        "build integrability-first gate for curl-free dust-image phi/L selection",
        "build no-go test for local scalar Phi family under split Noether and weak-field constraints",
        "build kinetic-sheet closure bridge from current dust proof to multistream matter",
    ]
    active_experiment_artifacts = [
        "p0_integrability_first_phi_l_selection",
        "p0_integrability_first_equation_system",
        "p0_integrability_regular_patch_toy_solver",
        "p0_local_phi_scouple_no_go_target",
        "p0_local_phi_scouple_symbolic_restricted_audit",
    ]
    return {
        "description": "Global P0 review and outside-the-box route map.",
        "status": "review-complete-outside-routes-open",
        "closed_work": closed_work,
        "open_blockers": open_blockers,
        "outside_box_routes": outside_box_routes,
        "next_experiments": next_experiments,
        "active_experiment_artifacts": active_experiment_artifacts,
        "published_janus_closed": False,
        "extension_axiom_adopted": False,
        "anti_rustine_gate_passed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The strongest non-rustine path is not to adopt A_phi_scouple immediately, "
            "but to try integrability/no-go/kinetic-sheet routes that either force a map "
            "or prove a new principle is unavoidable."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Global Review Outside-Box Routes",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Published Janus closed: {payload['published_janus_closed']}",
        f"Extension axiom adopted: {payload['extension_axiom_adopted']}",
        f"Anti-rustine gate passed: {payload['anti_rustine_gate_passed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Closed Work",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["closed_work"])
    lines.extend(["", "## Open Blockers", ""])
    for row in payload["open_blockers"]:
        lines.append(f"- {row['severity']} {row['blocker']}: {row['state']}")
    lines.extend(["", "## Outside-Box Routes", ""])
    for row in payload["outside_box_routes"]:
        lines.append(f"- {row['route']} ({row['classification']}): {row['idea']}")
        lines.append(f"  - acceptance: {row['acceptance']}")
        lines.append(f"  - risk: {row['risk']}")
    lines.extend(["", "## Next Experiments", ""])
    lines.extend(f"- {item}" for item in payload["next_experiments"])
    lines.extend(["", "## Active Experiment Artifacts", ""])
    lines.extend(f"- `{item}`" for item in payload["active_experiment_artifacts"])
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

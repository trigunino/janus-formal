from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_falpha_minimal_gauge_candidate.md")
JSON_PATH = Path("outputs/reports/p0_falpha_minimal_gauge_candidate.json")


def build_payload() -> dict:
    fixed_components = [
        {
            "component": "flow_force_projection",
            "condition": "u_to^beta F^A_{D beta} u_source^D cancels C^A_{BC}u_to^B u_to^C",
            "status": "conditional-equation",
        },
        {
            "component": "continuity_trace_projection",
            "condition": "F^A_{B A} u_source^B supplies transported continuity trace",
            "status": "conditional-equation",
        },
        {
            "component": "lorentz_generator",
            "condition": "Omega_alpha=(D_alpha L)L^{-1}, Omega_alpha^T eta + eta Omega_alpha=0",
            "status": "necessary-admissibility",
        },
    ]
    gauge_choice = [
        "set transverse/off-flow Lorentz-generator components to zero in the minimal diagnostic gauge",
        "allow nonzero transverse components only if Janus source geometry derives them",
        "mirror F_plus/F_minus from one inverse L, not by independent fitting",
    ]
    open_risks = [
        "minimal transverse-zero gauge may be too restrictive",
        "not source-derived from accepted Janus equations",
        "pressure/Pi orientation can reintroduce transverse components",
        "R_plus/R_minus closure still requires B_4vol branch and Cuu substitution",
    ]
    return {
        "description": "Minimal-gauge candidate for underdetermined F_alpha components.",
        "status": "minimal-gauge-candidate-open",
        "fixed_components": fixed_components,
        "gauge_choice": gauge_choice,
        "open_risks": open_risks,
        "minimal_gauge_declared": True,
        "source_derived_falpha": False,
        "all_transverse_components_fixed_by_source": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This gives the most economical F_alpha candidate: flow projections are "
            "fixed by dust equations and transverse components are zero-gauge unless "
            "Janus derives otherwise. It is not a source law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 F_alpha Minimal Gauge Candidate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Minimal gauge declared: {payload['minimal_gauge_declared']}",
        f"Source-derived F_alpha: {payload['source_derived_falpha']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Fixed Components",
        "",
    ]
    for row in payload["fixed_components"]:
        lines.append(f"- {row['component']}: `{row['condition']}` ({row['status']})")
    lines.extend(["", "## Gauge Choice", ""])
    lines.extend(f"- {item}" for item in payload["gauge_choice"])
    lines.extend(["", "## Open Risks", ""])
    lines.extend(f"- {item}" for item in payload["open_risks"])
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

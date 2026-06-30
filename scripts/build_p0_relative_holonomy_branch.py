from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_relative_holonomy_branch.md")
JSON_PATH = Path("outputs/reports/p0_relative_holonomy_branch.json")


def build_payload() -> dict:
    construction = [
        "allow R_Omega != 0 as relative holonomy between sector tetrad transports",
        "interpret path dependence of L as physical relative curvature information",
        "Q_cross and K must use the same path/family rule if holonomy is retained",
        "closed loops produce measurable consistency constraints, not fitted amplitudes",
    ]
    advantages = [
        "does not erase relative curvature between g_plus and g_minus",
        "may encode non-FLRW perturbative sector mismatch",
        "offers observables through loop/path consistency rather than scalar tuning",
    ]
    blockers = [
        "requires a source-derived path/family rule",
        "path-dependent Q_cross is not survey-ready without a declared light path prescription",
        "zero-divergence PDE must close for the same holonomy branch",
        "holonomy cannot be tuned to lensing data",
    ]
    return {
        "description": "P0 relative-holonomy branch for non-flat Omega transport.",
        "status": "relative-holonomy-branch-open",
        "nonflat_branch_written": True,
        "keeps_relative_curvature": True,
        "path_rule_source_derived": False,
        "zero_divergence_verified": False,
        "physics_closed": False,
        "prediction_ready": False,
        "construction": construction,
        "advantages": advantages,
        "blockers": blockers,
        "verdict": (
            "Relative holonomy is the honest non-flat alternative to pure gauge. It "
            "keeps possible physical curvature mismatch, but needs a source-derived "
            "path rule before it can support Q_cross or K predictions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Relative-Holonomy Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Keeps relative curvature: {payload['keeps_relative_curvature']}",
        f"Path rule source-derived: {payload['path_rule_source_derived']}",
        f"Zero-divergence verified: {payload['zero_divergence_verified']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Construction",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["construction"])
    lines.extend(["", "## Advantages", ""])
    lines.extend(f"- {item}" for item in payload["advantages"])
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

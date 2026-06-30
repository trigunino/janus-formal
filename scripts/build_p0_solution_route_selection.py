from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_solution_route_selection.md")
JSON_PATH = Path("outputs/reports/p0_solution_route_selection.json")


def build_payload() -> dict:
    routes = [
        {
            "route": "minimal_lorentz_dust",
            "status": "primary",
            "can_close_if": [
                "source-derived D L is obtained",
                "density measure B_4vol identity cancels residual terms",
                "same L gives K and Q_cross",
            ],
            "failure_mode": "dust-only branch cannot transport pressure or Pi",
            "accepted": False,
        },
        {
            "route": "cartan_integrability",
            "status": "parallel_candidate",
            "can_close_if": [
                "relative curvature R_Omega is source-derived",
                "flat case gives global pure-gauge L or non-flat case gives path rule",
                "loop consistency fixes holonomy without fitted amplitudes",
            ],
            "failure_mode": "path choice becomes an arbitrary lensing calibration",
            "accepted": False,
        },
        {
            "route": "variational_noether",
            "status": "parallel_candidate",
            "can_close_if": [
                "interaction action is source-derived from Janus",
                "Euler-Lagrange equations define L/K/Q_cross",
                "Noether identity implies both Bianchi residuals",
            ],
            "failure_mode": "new action becomes an extra axiom rather than a derivation",
            "accepted": False,
        },
        {
            "route": "kinetic_moment_extension",
            "status": "escalation_candidate",
            "can_close_if": [
                "Vlasov or moment hierarchy supplies pressure/Pi",
                "Pi orientation fixes residual screen gauge",
                "moment closure is not tuned to observations",
            ],
            "failure_mode": "matter extension patches missing L transport",
            "accepted": False,
        },
    ]
    promotion_tests = [
        "derive all required equations from accepted Janus sources or explicitly mark a new axiom",
        "prove tensor identity before using any scalar observable normalization",
        "substitute into R_plus and R_minus before claiming closure",
        "verify Q_det and Q_cross remain separate",
    ]
    return {
        "description": "P0 route-selection matrix for continuing toward a real Janus closure solution.",
        "status": "route-selection-open",
        "selected_route": None,
        "physics_closed": False,
        "prediction_ready": False,
        "routes": routes,
        "promotion_tests": promotion_tests,
        "recommended_parallel_work": [
            "continue minimal_lorentz_dust as critical path",
            "run cartan_integrability to decide flat versus holonomy",
            "run variational_noether only if source text supports an action identity",
            "hold kinetic_moment_extension until pressure/Pi is required",
        ],
        "verdict": (
            "The best current strategy is not one exotic jump but three controlled "
            "attempts: minimal dust, Cartan integrability, and variational Noether. "
            "A route is accepted only if it closes both residuals without fitted scalar shortcuts."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Solution Route Selection",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selected route: {payload['selected_route']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| route | status | can close if | failure mode | accepted |",
        "|---|---|---|---|---|",
    ]
    for row in payload["routes"]:
        lines.append(
            f"| {row['route']} | {row['status']} | {'; '.join(row['can_close_if'])} | "
            f"{row['failure_mode']} | {row['accepted']} |"
        )
    lines.extend(["", "## Promotion Tests", ""])
    lines.extend(f"- {item}" for item in payload["promotion_tests"])
    lines.extend(["", "## Recommended Parallel Work", ""])
    lines.extend(f"- {item}" for item in payload["recommended_parallel_work"])
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

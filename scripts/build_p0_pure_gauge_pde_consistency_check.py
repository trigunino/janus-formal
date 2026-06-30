from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pure_gauge_pde_consistency_check.md")
JSON_PATH = Path("outputs/reports/p0_pure_gauge_pde_consistency_check.json")


def build_payload() -> dict:
    branch = [
        "choose Lorentz-admissible L from projected raw solder map",
        "construct K_plus=L T_minus L^T and mirror K_minus",
        "insert S_plus=B_4vol_plus_from_minus K_plus into D_plus S_plus=0",
        "insert S_minus=B_4vol_minus_from_plus K_minus into D_minus S_minus=0",
    ]
    required_equalities = [
        "D_plus_nu(B_plus L_-+ T_minus L_-+^T)^{mu nu}=0",
        "D_minus_nu(B_minus L_+- T_plus L_+-^T)^{mu nu}=0",
        "same L branch defines Q_cross contractions",
        "Lorentz projection remains regular on the domain",
    ]
    pass_fail = [
        {
            "check": "Lorentz admissibility",
            "status": "can pass by construction after projection",
            "closes_physics": False,
        },
        {
            "check": "zero-divergence PDE",
            "status": "not automatic from pure-gauge construction",
            "closes_physics": False,
        },
        {
            "check": "Q_cross compatibility",
            "status": "requires same projected L and no independent optical scaling",
            "closes_physics": False,
        },
    ]
    return {
        "description": "P0 consistency check for pure-gauge L against the M30 zero-divergence PDE.",
        "status": "pure-gauge-pde-check-open",
        "check_written": True,
        "lorentz_admissible_conditionally": True,
        "zero_divergence_automatic": False,
        "physics_closed": False,
        "prediction_ready": False,
        "branch": branch,
        "required_equalities": required_equalities,
        "pass_fail": pass_fail,
        "verdict": (
            "Pure-gauge L may solve path ambiguity, but it does not automatically "
            "solve the M30 zero-divergence PDE. The next acceptance test is direct "
            "substitution into D(BK)=0."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pure-Gauge PDE Consistency Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz admissible conditionally: {payload['lorentz_admissible_conditionally']}",
        f"Zero divergence automatic: {payload['zero_divergence_automatic']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branch",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["branch"])
    lines.extend(["", "## Required Equalities", ""])
    lines.extend(f"- `{item}`" for item in payload["required_equalities"])
    lines.extend(["", "## Pass/Fail", ""])
    for row in payload["pass_fail"]:
        lines.append(f"- {row['check']}: {row['status']}; closes_physics={row['closes_physics']}")
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

from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_density_measure_identity_lock.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_density_measure_identity_lock.json")


def build_payload() -> dict:
    convention_rows = [
        {
            "item": "phi_jacobian_density",
            "rule": "rho_to = J_phi phi^* rho_source",
            "fixed": False,
        },
        {
            "item": "b_measure",
            "rule": "B is the density/volume measure used in B rho_to",
            "fixed": False,
        },
        {
            "item": "qdet_source_measure",
            "rule": "choose 4-volume or dust 3-volume before using Q_det",
            "fixed": False,
        },
        {
            "item": "qcross_separation",
            "rule": "Q_cross remains optical projection only",
            "fixed": True,
        },
    ]
    blocked_identities = [
        "sqrt|g_plus| J_phi = phi^* sqrt|g_minus|",
        "D log B = D log J_phi + transported metric-volume remainder",
        "D_receiver(B rho_to u_to)=0 from transported source continuity",
    ]
    return {
        "description": "Convention lock for D_phi density cancellation and DlogB volume absorption.",
        "status": "density-measure-identity-lock-open",
        "convention_rows": convention_rows,
        "blocked_identities": blocked_identities,
        "density_measure_convention_fixed": False,
        "qdet_qcross_separate": True,
        "effective_density_continuity_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "D_phi and DlogB can be tested only after one phi/J_phi/B/Q_det convention "
            "is locked. Q_cross remains separate and cannot absorb density terms."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Density Measure Identity Lock",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Density measure convention fixed: {payload['density_measure_convention_fixed']}",
        f"Q_det/Q_cross separate: {payload['qdet_qcross_separate']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| item | rule | fixed |",
        "|---|---|---|",
    ]
    for row in payload["convention_rows"]:
        lines.append(f"| {row['item']} | {row['rule']} | {row['fixed']} |")
    lines.extend(["", "## Blocked Identities", ""])
    lines.extend(f"- `{item}`" for item in payload["blocked_identities"])
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

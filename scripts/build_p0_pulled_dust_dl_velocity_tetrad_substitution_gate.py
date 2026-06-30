from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pulled_dust_dl_velocity_tetrad_substitution_gate.md")
JSON_PATH = Path("outputs/reports/p0_pulled_dust_dl_velocity_tetrad_substitution_gate.json")


def build_payload() -> dict:
    substitution_rows = [
        {
            "term": "antisymmetric D_L tetrad projection",
            "gate": "E_L plus Lorentz-generator law",
            "closed": False,
        },
        {
            "term": "symmetric D_L tetrad projection",
            "gate": "Lorentz constraint L^T eta L=eta",
            "closed": False,
        },
        {
            "term": "same-L K/Q_cross drift",
            "gate": "same L used for K_plus/K_minus and Q_cross",
            "closed": False,
        },
        {
            "term": "transported velocity acceleration",
            "gate": "transported geodesic and continuity equations",
            "closed": False,
        },
    ]
    outside_scope = [
        "connection-difference residual C_self-other u u",
        "D_phi density/measure cancellation",
        "pressure/Pi tensor extension",
    ]
    return {
        "description": "Substitution gate for the D_L velocity/tetrad row of pulled dust EL projection.",
        "status": "dl-velocity-tetrad-substitution-open",
        "substitution_rows": substitution_rows,
        "outside_scope": outside_scope,
        "dl_velocity_tetrad_interface_written": True,
        "all_dl_rows_closed": False,
        "connection_force_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The D_L velocity/tetrad interface is mapped to existing gates. It does not "
            "close the receiving-connection Cuu residual or any prediction claim."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pulled Dust DL Velocity/Tetrad Substitution Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"DL velocity/tetrad interface written: {payload['dl_velocity_tetrad_interface_written']}",
        f"All DL rows closed: {payload['all_dl_rows_closed']}",
        f"Connection force closed: {payload['connection_force_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| term | gate | closed |",
        "|---|---|---|",
    ]
    for row in payload["substitution_rows"]:
        lines.append(f"| {row['term']} | {row['gate']} | {row['closed']} |")
    lines.extend(["", "## Outside Scope", ""])
    lines.extend(f"- {item}" for item in payload["outside_scope"])
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

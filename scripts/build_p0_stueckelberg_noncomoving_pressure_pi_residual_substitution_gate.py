from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_noncomoving_pressure_pi_residual_substitution_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_noncomoving_pressure_pi_residual_substitution_gate.json")


def build_payload() -> dict:
    residual_terms = [
        {
            "sector": "positive",
            "substitution": "K_plus^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}+Pi^{mu nu}",
            "open_terms": ["D p", "D u", "D Pi", "T0i momentum", "connection-force pressure/Pi pieces"],
            "closed": False,
        },
        {
            "sector": "negative",
            "substitution": "K_minus^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}+Pi^{mu nu}",
            "open_terms": ["D p", "D u", "D Pi", "T0i momentum", "mirror connection-force pressure/Pi pieces"],
            "closed": False,
        },
    ]
    required_inputs = [
        "source-derived beta/gamma/u",
        "cross-sector p_cross or w_cross",
        "Pi00 and Pi0i transport or zero-proof",
        "projector derivative D h^{mu nu}",
        "same L_minus_to_plus used by K and Q_cross",
    ]
    forbidden_shortcuts = [
        "do not close pressure/Pi by scalar Q_det",
        "do not close pressure/Pi by scalar Q_cross",
        "do not use T00-only checks as momentum closure",
    ]
    return {
        "description": "Residual substitution gate for non-comoving pressure/Pi in both Bianchi sectors.",
        "status": "residual-substitution-gate-open",
        "residual_terms": residual_terms,
        "required_inputs": required_inputs,
        "forbidden_shortcuts": forbidden_shortcuts,
        "r_plus_pressure_pi_residual_closed": False,
        "r_minus_pressure_pi_residual_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Pressure/Pi is not closed until the explicit substituted terms vanish in "
            "both R_plus and R_minus, including momentum T0i."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Non-comoving Pressure/Pi Residual Substitution Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"R plus pressure/Pi residual closed: {payload['r_plus_pressure_pi_residual_closed']}",
        f"R minus pressure/Pi residual closed: {payload['r_minus_pressure_pi_residual_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Residual Terms",
        "",
    ]
    for row in payload["residual_terms"]:
        lines.append(f"- {row['sector']}: `{row['substitution']}` closed={row['closed']}")
        lines.extend(f"  - open: `{item}`" for item in row["open_terms"])
    lines.extend(["", "## Required Inputs", ""])
    lines.extend(f"- {item}" for item in payload["required_inputs"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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

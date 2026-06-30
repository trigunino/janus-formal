from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_connection_force_residual_target.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_connection_force_residual_target.json")


def build_payload() -> dict:
    residual_force_terms = [
        {
            "sector": "positive",
            "term": "C_plus-minus^mu_{nu alpha} rho_minus u_{-to+}^alpha u_{-to+}^nu",
            "after": "DlogB measure terms and DL velocity terms localized",
            "closed": False,
        },
        {
            "sector": "negative",
            "term": "C_minus-plus^mu_{nu alpha} rho_plus u_{+to-}^alpha u_{+to-}^nu",
            "after": "DlogB measure terms and DL velocity terms localized",
            "closed": False,
        },
    ]
    required_cancellations = [
        "derive relative connection C from the same Janus map that defines L",
        "show projected C u u terms equal the remaining Stueckelberg map-equation force",
        "prove mirror sign consistency between plus and minus residuals",
        "reinsert pressure/Pi connection terms before claiming tensor closure",
    ]
    blockers = [
        "D_alpha L remains source-open",
        "DlogB absorption remains conditional",
        "relative-connection contraction is not cancelled",
        "pressure/Pi extension is not closed",
    ]
    return {
        "description": "Target for the remaining relative-connection force in Stueckelberg residual closure.",
        "status": "connection-force-residual-open",
        "residual_force_terms": residual_force_terms,
        "required_cancellations": required_cancellations,
        "blockers": blockers,
        "connection_force_residual_localized": True,
        "connection_force_residual_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "After DlogB and DL localization, the hard remaining dust term is the "
            "relative-connection contraction on transported flows. It is not closed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Connection Force Residual Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Connection force residual localized: {payload['connection_force_residual_localized']}",
        f"Connection force residual closed: {payload['connection_force_residual_closed']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Residual Force Terms",
        "",
    ]
    for row in payload["residual_force_terms"]:
        lines.append(f"- {row['sector']}: `{row['term']}`")
        lines.append(f"  - after: {row['after']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Required Cancellations", ""])
    lines.extend(f"- {item}" for item in payload["required_cancellations"])
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

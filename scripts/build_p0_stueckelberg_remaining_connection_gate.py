from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_remaining_connection_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_remaining_connection_gate.json")


def build_payload() -> dict:
    remaining = [
        {
            "term": "C_plus-minus^mu_ab u_-to+^a u_-to+^b",
            "sector": "plus",
            "must_be": "zero or canceled by plus map equation",
            "closed": False,
        },
        {
            "term": "C_minus-plus^mu_ab u_+to-^a u_+to-^b",
            "sector": "minus",
            "must_be": "zero or canceled by minus map equation",
            "closed": False,
        },
    ]
    possible_closures = [
        {
            "route": "receiver_geodesic_transport",
            "condition": "phi/L maps source geodesics to receiver geodesics",
            "risk": "strong; may overconstrain phi/L",
        },
        {
            "route": "map_eom_force_balance",
            "condition": "E_phi/E_L produces exactly the connection-force residual",
            "risk": "requires explicit action variation",
        },
        {
            "route": "special_geometry",
            "condition": "relative connection contraction vanishes on transported dust flow",
            "risk": "may hold only in FLRW/symmetric branches",
        },
    ]
    return {
        "description": "Gate for the last zero-parameter Stueckelberg dust connection residual.",
        "status": "remaining-connection-gate-open",
        "all_density_terms_reduced": True,
        "dlogb_absorbed_conditionally": True,
        "dl_terms_localized": True,
        "connection_residual_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "remaining": remaining,
        "possible_closures": possible_closures,
        "acceptance": [
            "same phi/L must close both sectors",
            "no observational boundary tuning",
            "no independent Q_cross map",
            "must work beyond a purely FLRW diagnostic if used as tensor proof",
        ],
        "verdict": (
            "The remaining hard blocker is narrow: the relative-connection contraction "
            "on transported dust flows. Closing it requires receiver-geodesic transport, "
            "map-EOM force balance, or a proved special-geometry identity."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Remaining Connection Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All density terms reduced: {payload['all_density_terms_reduced']}",
        f"DlogB absorbed conditionally: {payload['dlogb_absorbed_conditionally']}",
        f"D_L terms localized: {payload['dl_terms_localized']}",
        f"Connection residual closed: {payload['connection_residual_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Remaining Terms",
        "",
    ]
    for row in payload["remaining"]:
        lines.append(f"- {row['sector']}: `{row['term']}` must be {row['must_be']}; closed={row['closed']}")
    lines.extend(["", "## Possible Closures", ""])
    for row in payload["possible_closures"]:
        lines.append(f"- {row['route']}: {row['condition']} (risk: {row['risk']})")
    lines.extend(["", "## Acceptance", ""])
    lines.extend(f"- {item}" for item in payload["acceptance"])
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

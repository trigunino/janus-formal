from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_projected_cuu_map_force_balance.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_projected_cuu_map_force_balance.json")


def build_payload() -> dict:
    projected_identities = [
        {
            "sector": "positive",
            "identity": "Proj_perp(E_phi/E_L)_plus = rho_minus h_plus C_plus-minus(u_-to+,u_-to+)",
            "role": "cancel plus projected dust connection force",
            "derived_from_action": False,
        },
        {
            "sector": "negative",
            "identity": "Proj_perp(E_phi/E_L)_minus = rho_plus h_minus C_minus-plus(u_+to-,u_+to-)",
            "role": "cancel minus projected dust connection force",
            "derived_from_action": False,
        },
    ]
    required_checks = [
        "derive projected identity from Stueckelberg E_phi/E_L",
        "prove plus/minus mirror consistency from one phi/L pair",
        "close curl/integrability on dust image distribution",
        "state pressure/Pi is out of this dust-only force balance",
        "do not impose weak congruence as an independent axiom",
    ]
    return {
        "description": "Projected map-force balance target for cancelling Cuu dust residuals.",
        "status": "projected-force-balance-open",
        "projected_identities": projected_identities,
        "required_checks": required_checks,
        "projected_identity_written": True,
        "derived_from_action": False,
        "mirror_consistency_closed": False,
        "integrability_closed": False,
        "dust_connection_force_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is the exact identity to prove or falsify next. It is not closure: "
            "current status is a projected dust target, not an action-derived result."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Projected Cuu Map Force Balance",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Projected identity written: {payload['projected_identity_written']}",
        f"Derived from action: {payload['derived_from_action']}",
        f"Dust connection force closed: {payload['dust_connection_force_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Projected Identities",
        "",
    ]
    for row in payload["projected_identities"]:
        lines.append(f"- {row['sector']}: `{row['identity']}`")
        lines.append(f"  - role: {row['role']}")
        lines.append(f"  - derived from action: {row['derived_from_action']}")
    lines.extend(["", "## Required Checks", ""])
    lines.extend(f"- {item}" for item in payload["required_checks"])
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

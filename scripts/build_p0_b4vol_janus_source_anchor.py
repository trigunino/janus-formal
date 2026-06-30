from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_b4vol_janus_source_anchor.md")
JSON_PATH = Path("outputs/reports/p0_b4vol_janus_source_anchor.json")


def build_payload() -> dict:
    source_rows = [
        {
            "id": "S1",
            "source": "M15 Eqs. 4a-4b",
            "formula": "G_plus = chi(T_plus + sqrt(-g_minus/-g_plus) T_minus)",
            "role": "selects B_4vol_minus_to_plus as the plus-equation cross-source measure",
            "closed": True,
        },
        {
            "id": "S2",
            "source": "M15 Eqs. 4a-4b",
            "formula": "G_minus = -chi(sqrt(-g_plus/-g_minus) T_plus + T_minus)",
            "role": "selects B_4vol_plus_to_minus as the mirror cross-source measure",
            "closed": True,
        },
        {
            "id": "S3",
            "source": "M30 Eqs. 105a-105b",
            "formula": "mixed stationary form keeps determinant-weighted cross-source layer",
            "role": "later-source consistency check for the same active source slot",
            "closed": True,
        },
    ]
    remaining_rows = [
        "derive the same B_4vol from the pulled dust action, not only the field equation RHS",
        "prove the phi/L map used for B_4vol is the same map used in u_to and Cuu",
        "prove plus/minus inverse consistency for the two determinant ratios",
        "extend beyond dust before using pressure or Pi",
    ]
    return {
        "description": "Source anchor for B_4vol as the Janus active cross-source measure.",
        "status": "field-source-anchor-closed-action-bridge-open",
        "source_rows": source_rows,
        "remaining_rows": remaining_rows,
        "b4vol_field_source_anchor_closed": True,
        "b4vol_pulled_action_anchor_closed": False,
        "single_cross_dust_continuity_admissible": True,
        "full_two_sector_bianchi_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Janus source equations select B_4vol in the active cross-source slot. "
            "This closes the source-measure anchor for the pulled dust continuity theorem, "
            "but not the full action/phi/L/mirror bridge."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 B4vol Janus Source Anchor",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B4vol field-source anchor closed: {payload['b4vol_field_source_anchor_closed']}",
        f"B4vol pulled-action anchor closed: {payload['b4vol_pulled_action_anchor_closed']}",
        f"Single cross-dust continuity admissible: {payload['single_cross_dust_continuity_admissible']}",
        f"Full two-sector Bianchi closed: {payload['full_two_sector_bianchi_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Rows",
        "",
    ]
    for row in payload["source_rows"]:
        lines.append(f"- {row['id']} ({row['source']}): `{row['formula']}`")
        lines.append(f"  - role: {row['role']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Remaining Rows", ""])
    lines.extend(f"- {item}" for item in payload["remaining_rows"])
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

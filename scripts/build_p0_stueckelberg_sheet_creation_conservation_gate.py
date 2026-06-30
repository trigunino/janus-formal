from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_sheet_creation_conservation_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_sheet_creation_conservation_gate.json")


def build_payload() -> dict:
    conservation_rules = [
        {
            "name": "mass_weight_conservation",
            "rule": "sum_s rho_s_to dV_s equals the pre-caustic transported mass measure",
            "status": "required-not-proved",
        },
        {
            "name": "momentum_sheet_balance",
            "rule": "sum_s rho_s_to u_s_to^mu dV_s is inherited from the limiting phase-space flow",
            "status": "required-not-proved",
        },
        {
            "name": "no_new_lensing_weight",
            "rule": "sheet optical contribution uses transported sheet weight only",
            "status": "enforced",
        },
        {
            "name": "mirror_sheet_pairing",
            "rule": "each plus-supported sheet has a minus mirror support or is flagged non-closed",
            "status": "required-not-proved",
        },
    ]
    forbidden = [
        "choosing sheet count to fit observations",
        "choosing sheet weights independently of transported density-volume",
        "assigning separate Q_cross amplitude per sheet",
        "dropping mirror-inconsistent sheets silently",
    ]
    decision = {
        "sheet_creation_rule_defined": True,
        "conservation_closed": False,
        "new_fit_parameters": False,
        "prediction_ready": False,
        "reason": (
            "Sheet creation must be treated as a conservative limit of the dust flow. "
            "The model can be diagnostic, but mass/momentum weights and mirror pairing "
            "must be derived before any post-caustic prediction."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_sheet_creation_conservation_gate",
        "status": "sheet-creation-conservation-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "conservation_rules": conservation_rules,
        "forbidden": forbidden,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Sheet Creation Conservation Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Conservation Rules",
    ]
    for row in payload["conservation_rules"]:
        lines.append(f"- {row['name']}: {row['rule']} (status={row['status']})")
    lines.extend(["", "## Forbidden"])
    lines.extend(f"- {item}" for item in payload["forbidden"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Sheet creation rule defined: {decision['sheet_creation_rule_defined']}",
            f"Conservation closed: {decision['conservation_closed']}",
            f"New fit parameters: {decision['new_fit_parameters']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")

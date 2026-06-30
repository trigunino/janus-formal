from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_transport_branch_closure_obligations.md")
JSON_PATH = Path("outputs/reports/p0_transport_branch_closure_obligations.json")


def build_payload() -> dict:
    obligations = [
        {
            "name": "admissible_L",
            "requires": [
                "Lorentz/tetrad condition for the transported map",
                "regular branch or source-derived holonomy path rule",
                "no fitted branch switching",
            ],
            "closed": False,
        },
        {
            "name": "D_L",
            "requires": [
                "covariant derivative of the selected L, not of a discarded raw map",
                "projection/holonomy derivative terms retained",
                "source equation or identity fixing residual gauge freedom",
            ],
            "closed": False,
        },
        {
            "name": "same_L_for_K_and_Q_cross",
            "requires": [
                "K_plus/K_minus transport and optical Q_cross use the same selected L",
                "no scalar absorption into Q_det or Q_cross",
                "same path/family rule in non-flat holonomy branches",
            ],
            "closed": False,
        },
        {
            "name": "R_plus_R_minus",
            "requires": [
                "substitute full tensor K families into both Bianchi residuals",
                "prove R_plus=0 and R_minus=0 without fitted residuals",
                "keep pressure and anisotropic-stress terms tensorial",
            ],
            "closed": False,
        },
    ]
    return {
        "description": "Wide-pass P0 obligations linking L branches to tensor residual closure.",
        "status": "closure-obligations-open",
        "physics_closed": False,
        "prediction_ready": False,
        "obligations": obligations,
        "forbidden_shortcuts": [
            "using polar projection regularity as source derivation",
            "choosing holonomy paths from lensing fit residuals",
            "absorbing tensor transport failures into Q_det or Q_cross",
            "claiming R_plus/R_minus closure before pressure/Pi terms are transported",
        ],
        "next_derivations": [
            "derive D_alpha L for the selected branch",
            "derive K_plus/K_minus from the same selected L",
            "derive Q_cross from the same selected L/path rule",
            "substitute into R_plus and R_minus and require both vanish",
        ],
        "verdict": (
            "The broad branch work is useful only as a filter. Prediction remains blocked "
            "until one selected L branch supplies D L, K transport, Q_cross transport, "
            "and both Bianchi residuals without scalar shortcuts."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Transport Branch Closure Obligations",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| obligation | requires | closed |",
        "|---|---|---|",
    ]
    for row in payload["obligations"]:
        lines.append(f"| {row['name']} | {'; '.join(row['requires'])} | {row['closed']} |")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Next Derivations", ""])
    lines.extend(f"- {item}" for item in payload["next_derivations"])
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

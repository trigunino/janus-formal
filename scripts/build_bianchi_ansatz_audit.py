from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_ansatz_audit.md")
JSON_PATH = Path("outputs/reports/bianchi_ansatz_audit.json")


def build_payload() -> dict:
    residual_equations = [
        {
            "sector": "positive",
            "equation": (
                "R_plus^mu = D_plus_nu T_plus^{mu nu} "
                "+ B_plus(D_minus_nu K_plus^{mu nu} + C^mu_{nu a}K_plus^{a nu})"
            ),
            "target": "R_plus^mu = 0",
        },
        {
            "sector": "negative",
            "equation": (
                "R_minus^mu = D_minus_nu T_minus^{mu nu} "
                "+ B_minus(D_plus_nu K_minus^{mu nu} - C^mu_{nu a}K_minus^{a nu})"
            ),
            "target": "R_minus^mu = 0",
        },
    ]
    ansatz_rows = [
        {
            "ansatz": "naive_cross_copy",
            "definition": "K_plus=T_minus and K_minus=T_plus",
            "status": "not closed",
            "failure": "does not cancel cross-connection force terms C.K in general",
            "allowed_use": "none for tensor lensing",
        },
        {
            "ansatz": "weak_field_effective_density",
            "definition": "B_plus ~= 1 and K_plus/K_minus reduced to Newtonian effective densities",
            "status": "diagnostic only",
            "failure": "only asymptotic/weak-field; not full D_plus/D_minus closure",
            "allowed_use": "PM sign dynamics and source diagnostics",
        },
        {
            "ansatz": "flrw_or_stationary_special",
            "definition": "special symmetry branch with reduced connection structure",
            "status": "branch target",
            "failure": "does not imply generic non-perturbative closure",
            "allowed_use": "derive and test as a named branch only",
        },
        {
            "ansatz": "unknown_mixed_transport",
            "definition": "K tensors include metric-volume, cross-map, pressure/stress and connection-difference transport",
            "status": "required target",
            "failure": "not yet derived",
            "allowed_use": "next derivation target",
        },
    ]
    required_properties = [
        "K_plus/K_minus must be tensorial on the sector where their divergence is taken",
        "determinant derivatives must be handled through B_plus/B_minus, not inserted twice",
        "cross-map choices must agree with Q_cross optical projection target",
        "dust, perfect-fluid and anisotropic-stress contractions must remain distinct",
        "both R_plus^mu=0 and R_minus^mu=0 must hold, not only one sector",
    ]
    return {
        "description": "Audit of candidate Bianchi closure ansatz branches.",
        "source_anchors": [
            "M15 determinant-coupled field equations",
            "M30 Bianchi/asymptotic closure discussion",
            "local Q_det/Q_cross derivation targets",
        ],
        "physics_closed": False,
        "residual_equations": residual_equations,
        "ansatz_rows": ansatz_rows,
        "required_properties": required_properties,
        "verdict": (
            "No simple copied-stress ansatz closes the generic system. The next valid "
            "target is a mixed-transport K_plus/K_minus construction satisfying both residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Ansatz Audit",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Residual Equations",
        "",
        "| sector | equation | target |",
        "|---|---|---|",
    ]
    for row in payload["residual_equations"]:
        lines.append(f"| {row['sector']} | `{row['equation']}` | `{row['target']}` |")
    lines.extend(
        [
            "",
            "## Ansatz Rows",
            "",
            "| ansatz | definition | status | failure | allowed use |",
            "|---|---|---|---|---|",
        ]
    )
    for row in payload["ansatz_rows"]:
        lines.append(
            f"| {row['ansatz']} | `{row['definition']}` | {row['status']} | "
            f"{row['failure']} | {row['allowed_use']} |"
        )
    lines.extend(["", "## Required Properties", ""])
    lines.extend(f"- {item}" for item in payload["required_properties"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

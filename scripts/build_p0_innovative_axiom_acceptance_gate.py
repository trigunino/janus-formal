from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_innovative_axiom_acceptance_gate.md")
JSON_PATH = Path("outputs/reports/p0_innovative_axiom_acceptance_gate.json")


def build_payload() -> dict:
    gates = [
        {
            "gate": "mathematical_consistency",
            "requires": [
                "well-defined covariant variables",
                "symmetric interaction tensors",
                "no overdetermined residual equations",
            ],
            "passed": False,
        },
        {
            "gate": "janus_compatibility",
            "requires": [
                "recovers M15/M30 weak-field signs",
                "keeps two geodesic families",
                "preserves determinant-density conventions",
            ],
            "passed": False,
        },
        {
            "gate": "no_fit_policy",
            "requires": [
                "no lensing/growth tuned potentials",
                "no survey-normalized constants",
                "boundary/gauge data specified before observations",
            ],
            "passed": False,
        },
        {
            "gate": "prediction_unlock",
            "requires": [
                "R_plus=0",
                "R_minus=0",
                "same L for K and Q_cross",
                "pressure/Pi extension not contradicted",
            ],
            "passed": False,
        },
    ]
    return {
        "description": "Acceptance gate for innovative Janus closure axioms or ansatz branches.",
        "status": "innovative-axiom-gate-open",
        "new_axiom_allowed_as_research": True,
        "new_axiom_accepted": False,
        "physics_closed": False,
        "prediction_ready": False,
        "gates": gates,
        "allowed_branches": [
            "Stueckelberg/two-diffeomorphism map",
            "constrained zero-divergence K solver",
            "auxiliary-L variational action",
        ],
        "rejection_rules": [
            "reject if it only restates zero divergence without solving K",
            "reject if it fits an observable residual",
            "reject if Q_cross is independent of the K transport map",
            "reject if it breaks the known Newtonian sign laws",
        ],
        "verdict": (
            "Innovative branches are allowed, but only as labelled axioms until they "
            "pass all gates. No branch unlocks predictions before both residuals close."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Innovative Axiom Acceptance Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"New axiom allowed as research: {payload['new_axiom_allowed_as_research']}",
        f"New axiom accepted: {payload['new_axiom_accepted']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| gate | requires | passed |",
        "|---|---|---|",
    ]
    for row in payload["gates"]:
        lines.append(f"| {row['gate']} | {'; '.join(row['requires'])} | {row['passed']} |")
    lines.extend(["", "## Allowed Branches", ""])
    lines.extend(f"- {item}" for item in payload["allowed_branches"])
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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

from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_variational_source_template_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_variational_source_template_gate.json")


def build_payload() -> dict:
    required_ingredients = [
        {
            "ingredient": "action variables",
            "requirement": "S_Janus[H, L, phi, matter] declares which fields are varied or held fixed",
            "closed": False,
        },
        {
            "ingredient": "variation domain",
            "requirement": "allowed delta H lives in the symmetric trace-free channel after gauge constraints",
            "closed": False,
        },
        {
            "ingredient": "boundary terms",
            "requirement": "integrations by parts and boundary/initial data are fixed before reading the EL source",
            "closed": False,
        },
        {
            "ingredient": "gauge constraints",
            "requirement": "lapse/slice/Lorentz or diffeo gauge constraints are imposed without removing H_TF",
            "closed": False,
        },
        {
            "ingredient": "same-L",
            "requirement": "the same L used by the Janus stack is used in the H_TF/Q_TF source equation",
            "closed": False,
        },
        {
            "ingredient": "mirror inverse",
            "requirement": "plus/minus variation obeys the mirror inverse branch, not independent H sources",
            "closed": False,
        },
        {
            "ingredient": "ghost/stability",
            "requirement": "principal symbol and physical-mode stability pass before prediction use",
            "closed": False,
        },
        {
            "ingredient": "source traceability",
            "requirement": "every S_TF term is traceable to S_Janus, matter variation, or an accepted source action",
            "closed": False,
        },
    ]
    return {
        "description": (
            "Bounded P0 template for accepting a variational trace-free H_TF/Q_TF "
            "source equation."
        ),
        "status": "tracefree-h-variational-source-template-gate-open",
        "target_source_equations": [
            "P_STF(delta S_Janus/delta H)=0",
            "P_STF(E_H - S_TF)=0",
        ],
        "target_source_rule": (
            "The H_TF/Q_TF source must be obtained by varying S_Janus with "
            "respect to H and then applying P_STF; an equivalent split form is "
            "P_STF(E_H - S_TF)=0."
        ),
        "action_variables": ["H", "L", "phi", "matter"],
        "required_ingredients": required_ingredients,
        "requirements_closed": False,
        "ultralocal_potential": {
            "action_class": "ultralocal potential V(H)",
            "sufficient_alone": False,
            "reason": "no derivative operator, boundary terms, gauge domain, same-L, mirror inverse, or stability proof",
        },
        "derivative_action": {
            "action_classes": ["D H action", "D Q_TF action"],
            "acceptance": "conditional",
            "condition": "accepted only after all required ingredients close",
        },
        "target_residual_source_allowed": False,
        "forbidden_routes": [
            "declare or fit a target residual source for H_TF/Q_TF",
            "use an ultralocal V(H) alone as the source template",
            "vary H with independent plus/minus or non-same-L branches",
        ],
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "No variational H_TF/Q_TF source template is accepted yet. The only "
            "admissible target is the STF projection of delta S_Janus/delta H "
            "or P_STF(E_H - S_TF)=0; residual targets are forbidden."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Variational Source Template Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target residual source allowed: {payload['target_residual_source_allowed']}",
        f"Requirements closed: {payload['requirements_closed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Target Source Equation",
        "",
    ]
    lines.extend(f"- `{equation}`" for equation in payload["target_source_equations"])
    lines.extend(
        [
            "",
            payload["target_source_rule"],
            "",
            "## Action Variables",
            "",
        ]
    )
    lines.extend(f"- `{item}`" for item in payload["action_variables"])
    lines.extend(
        [
            "",
            "## Required Ingredients",
            "",
            "| ingredient | requirement | closed |",
            "|---|---|---:|",
        ]
    )
    for row in payload["required_ingredients"]:
        lines.append(
            f"| {row['ingredient']} | {row['requirement']} | {row['closed']} |"
        )
    lines.extend(["", "## Ultralocal Potential", ""])
    for key, value in payload["ultralocal_potential"].items():
        lines.append(f"- {key}: `{value}`")
    derivative = payload["derivative_action"]
    lines.extend(["", "## Derivative Action", ""])
    lines.append(f"- action classes: `{', '.join(derivative['action_classes'])}`")
    lines.append(f"- acceptance: `{derivative['acceptance']}`")
    lines.append(f"- condition: {derivative['condition']}")
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_routes"])
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

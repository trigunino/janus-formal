from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_mirror_phi_constraints.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_mirror_phi_constraints.json")


def build_payload() -> dict:
    constraints = [
        {
            "name": "plus-minus mirror symmetry",
            "requirement": "Phi_bar is the mirror transform of Phi under plus <-> minus exchange",
            "effect": "removes independent choice of Phi_bar but does not uniquely fix Phi",
        },
        {
            "name": "determinant density convention",
            "requirement": "use sqrt(-g_plus) Phi in the plus action and sqrt(-g_minus) Phi_bar in the mirror action",
            "effect": "keeps each sector density native to its own metric",
        },
        {
            "name": "same L for K/Q_cross",
            "requirement": "the L field entering K_plus/K_minus transport is the same L used in Q_cross",
            "effect": "forbids a separate optical-map parameter",
        },
        {
            "name": "Newtonian sign recovery",
            "requirement": "weak-field dust limit must recover the intended plus/minus interaction sign",
            "effect": "filters allowed normalizations and signs of Phi",
        },
        {
            "name": "no free observational parameters",
            "requirement": "Phi may not introduce fit constants beyond fixed theory constants and sourced fields",
            "effect": "blocks phenomenological tuning",
        },
    ]
    return {
        "description": (
            "Bounded P0 artifact constraining Phi/Phi_bar in the explicit "
            "Stueckelberg action without claiming source-derived closure."
        ),
        "artifact": "stueckelberg-mirror-phi-constraints",
        "status": "bounded-constraints-open",
        "source_derived": False,
        "new_axiom_risk": True,
        "prediction_ready": False,
        "mirror_symmetry_imposed": True,
        "determinant_density_convention_fixed": True,
        "same_l_for_k_and_qcross": True,
        "newtonian_sign_recovery_required": True,
        "no_free_observational_parameters": True,
        "constraints_uniquely_fix_phi": False,
        "constraints": constraints,
        "acceptance_next": [
            "write the explicit mirror transform mapping Phi to Phi_bar",
            "derive K_plus/K_minus from the constrained action",
            "verify the weak-field Newtonian sign with the same L used in Q_cross",
            "prove no hidden fit parameters enter Phi",
            "decide whether an additional principle fixes Phi uniquely",
        ],
        "verdict": (
            "Mirror symmetry, density convention, shared L, Newtonian sign recovery, "
            "and no-fit requirements constrain Phi/Phi_bar but do not uniquely fix "
            "Phi. The branch remains source_derived=false, new_axiom_risk=true, "
            "and prediction_ready=false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Mirror Phi Constraints",
        "",
        payload["description"],
        "",
        f"Artifact: {payload['artifact']}",
        f"Status: {payload['status']}",
        f"Source derived: {payload['source_derived']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Mirror symmetry imposed: {payload['mirror_symmetry_imposed']}",
        f"Determinant density convention fixed: {payload['determinant_density_convention_fixed']}",
        f"Same L for K and Q_cross: {payload['same_l_for_k_and_qcross']}",
        f"Newtonian sign recovery required: {payload['newtonian_sign_recovery_required']}",
        f"No free observational parameters: {payload['no_free_observational_parameters']}",
        f"Constraints uniquely fix Phi: {payload['constraints_uniquely_fix_phi']}",
        "",
        "## Constraints",
        "",
        "| name | requirement | effect |",
        "|---|---|---|",
    ]
    for row in payload["constraints"]:
        lines.append(f"| {row['name']} | {row['requirement']} | {row['effect']} |")
    lines.extend(["", "## Acceptance Next", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_next"])
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

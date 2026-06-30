from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_minimal_axiom_transport_solution.md")
JSON_PATH = Path("outputs/reports/p0_minimal_axiom_transport_solution.json")


def build_payload() -> dict:
    axioms = [
        {
            "id": "A1",
            "name": "field-equation densitized source",
            "statement": "S_plus^{mu nu}=B_4vol_plus_from_minus K_plus^{mu nu}; S_minus^{mu nu}=B_4vol_minus_from_plus K_minus^{mu nu}",
            "effect": "D log B_4vol terms are kept inside D S, not dropped or reused as Q_det",
        },
        {
            "id": "A2",
            "name": "Lorentz transport map",
            "statement": "D_alpha L_minus_to_plus=F_alpha L_minus_to_plus with F_alpha^T eta + eta F_alpha=0",
            "effect": "L preserves tetrad inner products used by K and Q_cross",
        },
        {
            "id": "A3",
            "name": "mirror inverse transport",
            "statement": "L_plus_to_minus=L_minus_to_plus^{-1}; D L_plus_to_minus=-L_plus_to_minus(D L_minus_to_plus)L_plus_to_minus",
            "effect": "plus/minus residuals use one mirrored transport structure",
        },
        {
            "id": "A4",
            "name": "densitized Bianchi transport",
            "statement": "D_plus_nu S_plus^{mu nu}=0 and D_minus_nu S_minus^{mu nu}=0",
            "effect": "R_plus and R_minus close if same-sector matter is conserved",
        },
        {
            "id": "A5",
            "name": "same L for optics and stress",
            "statement": "the L used to build K_plus/K_minus is the L used in Q_cross contractions",
            "effect": "prevents independent lensing normalization",
        },
    ]
    closure_reduction = [
        "R_plus^mu=D_plus_nu(T_plus^{mu nu}+S_plus^{mu nu})",
        "A4_plus: D_plus_nu S_plus^{mu nu}=0",
        "if D_plus_nu T_plus^{mu nu}=0 and D_plus_nu S_plus^{mu nu}=0, then R_plus^mu=0",
        "R_minus^mu=D_minus_nu(S_minus^{mu nu}+T_minus^{mu nu})",
        "A4_minus: D_minus_nu S_minus^{mu nu}=0",
        "if D_minus_nu T_minus^{mu nu}=0 and D_minus_nu S_minus^{mu nu}=0, then R_minus^mu=0",
    ]
    not_yet_solved = [
        "derive A2-A4 from Janus action/source equations rather than postulating them",
        "construct explicit F_alpha for non-comoving perturbed flows",
        "show A4 follows from transported continuity and receiver-geodesic equations",
        "extend S_plus/S_minus to pressure, projector h, and Pi without scalar absorption",
        "derive observable Q_cross normalization after the same L is fixed",
    ]
    rejection_rules = [
        "do not multiply S_plus/S_minus by Q_det again",
        "do not replace B_4vol by V3_dust inside field equations",
        "do not set F_alpha=0 unless A2 is source-derived as parallel transport",
        "do not claim source proof from this axiom branch",
    ]
    return {
        "description": "Minimal axiom branch that would close R_plus/R_minus if adopted and later source-derived.",
        "status": "conditional-solution-branch",
        "axiom_branch_written": True,
        "conditional_r_plus_closed": True,
        "conditional_r_minus_closed": True,
        "source_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "axioms": axioms,
        "closure_reduction": closure_reduction,
        "not_yet_solved": not_yet_solved,
        "rejection_rules": rejection_rules,
        "verdict": (
            "This is the cleanest current solution candidate: make the field-equation "
            "source densitized and require its covariant divergence to vanish. It "
            "closes the residuals conditionally, but remains an axiom branch until "
            "derived from Janus sources."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Minimal Axiom Transport Solution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Conditional R_plus closed: {payload['conditional_r_plus_closed']}",
        f"Conditional R_minus closed: {payload['conditional_r_minus_closed']}",
        f"Source-derived: {payload['source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Axioms",
        "",
    ]
    for row in payload["axioms"]:
        lines.append(f"- {row['id']} {row['name']}: `{row['statement']}`")
        lines.append(f"  - effect: {row['effect']}")
    lines.extend(["", "## Closure Reduction", ""])
    lines.extend(f"- `{item}`" for item in payload["closure_reduction"])
    lines.extend(["", "## Not Yet Solved", ""])
    lines.extend(f"- {item}" for item in payload["not_yet_solved"])
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

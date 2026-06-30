from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_local_phi_scouple_no_go_target.md")
JSON_PATH = Path("outputs/reports/p0_local_phi_scouple_no_go_target.json")


def build_payload() -> dict:
    assumptions = [
        {
            "assumption": "locality",
            "classification": "scope restriction",
            "role": "Phi and S_couple depend on local fields/invariants only, with no history or nonlocal kernels.",
        },
        {
            "assumption": "low_derivative",
            "classification": "scope restriction",
            "role": "candidate terms are bounded to the low-derivative family used by current P0 closure attempts.",
        },
        {
            "assumption": "mirror_symmetry",
            "classification": "structural symmetry",
            "role": "plus/minus exchange fixes the mirror partner once a candidate is chosen.",
        },
        {
            "assumption": "M15_B_4vol",
            "classification": "source-measure anchor",
            "role": "M15 determinant cross-source factors set the B_4vol weighting target.",
        },
        {
            "assumption": "same_L_for_K_and_Qcross",
            "classification": "transport coherence",
            "role": "the same L must serve K transport and optical Q_cross coupling.",
        },
        {
            "assumption": "weak_field_sign",
            "classification": "linear-limit filter",
            "role": "Newtonian/weak-field sign recovery eliminates wrong-sign branches.",
        },
        {
            "assumption": "split_Noether_R_plus_R_minus",
            "classification": "closure test",
            "role": "substituted Noether residuals must close separately for R_plus and R_minus.",
        },
    ]
    if_proved_eliminates = [
        "would rule out rustine Phi/S_couple completions inside the bounded local low-derivative class",
        "would convert the current family obstruction into a negative theorem for that class",
        "would force any surviving completion to leave at least one stated assumption or declare a new axiom",
        "would block prediction_ready from being unlocked by ad hoc local counterterms",
    ]
    remaining_family_risks = [
        "higher-derivative local invariants outside the bound could remain",
        "nonlocal or history-dependent kernels could evade the theorem scope",
        "mirror-symmetric scalar functions not covered by the derivative bound may survive",
        "new source axioms or independent L/Q_cross maps could create a different family",
    ]
    return {
        "description": "Bounded P0 no-go theorem target for the local low-derivative Phi/S_couple family.",
        "status": "target-not-proved",
        "theorem_statement": (
            "Target: under locality, low derivative order, mirror symmetry, M15 B_4vol anchoring, "
            "same L for K/Q_cross, weak-field sign recovery, and split Noether R_plus/R_minus closure, "
            "no free local Phi/S_couple completion remains available."
        ),
        "assumptions": assumptions,
        "if_proved_eliminates": if_proved_eliminates,
        "remaining_family_risks": remaining_family_risks,
        "bounded_scope": "local-low-derivative-only",
        "theorem_proved": False,
        "rustine_eliminated_if_proved": True,
        "family_obstruction_eliminated_if_proved": True,
        "remaining_family_possible": True,
        "restricted_symbolic_audit_available": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is a theorem target, not a proof. It records the assumptions that would make a "
            "local low-derivative Phi/S_couple no-go result useful against rustine/family obstruction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Local Phi/S_couple No-Go Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Bounded scope: {payload['bounded_scope']}",
        f"Theorem proved: {payload['theorem_proved']}",
        f"Rustine eliminated if proved: {payload['rustine_eliminated_if_proved']}",
        f"Family obstruction eliminated if proved: {payload['family_obstruction_eliminated_if_proved']}",
        f"Remaining family possible: {payload['remaining_family_possible']}",
        f"Restricted symbolic audit available: {payload['restricted_symbolic_audit_available']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        f"Theorem target: {payload['theorem_statement']}",
        "",
        "## Assumptions",
        "",
        "| assumption | classification | role |",
        "|---|---|---|",
    ]
    for row in payload["assumptions"]:
        lines.append(f"| {row['assumption']} | {row['classification']} | {row['role']} |")
    lines.extend(["", "## If Proved Eliminates", ""])
    lines.extend(f"- {item}" for item in payload["if_proved_eliminates"])
    lines.extend(["", "## Remaining Family Risks", ""])
    lines.extend(f"- {item}" for item in payload["remaining_family_risks"])
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

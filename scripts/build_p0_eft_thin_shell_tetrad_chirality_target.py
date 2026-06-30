from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_thin_shell_tetrad_chirality_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_thin_shell_tetrad_chirality_target.json")


def build_payload() -> dict:
    tetrad_transition = {
        "source": "Z2 orbifold isometry exchanging Janus sheets across Sigma",
        "cartan_object": "global solder form I = E_plus^a tensor E_minus^b eta_ab",
        "normal_rule": "PT reverses the membrane normal",
        "target": "PT(E_plus^0)|_Sigma = -E_minus^0",
        "status": "target-not-derived",
    }
    thin_shell = {
        "operator": "Dirac-Cartan operator with q_T=1 trace-torsion shell term",
        "shell_source": "radion gradient d chi contains a delta(Sigma) contribution",
        "integration": "integrate D_JC psi across [-epsilon,+epsilon] normal to Sigma",
        "jump_condition_target": "spinor jump equals a local boundary projector condition",
        "chirality_target": "P_chiral psi|_Sigma = 0 for P_chiral=(1 +/- gamma5)/2",
        "aps_equivalence_target": "chiral shell condition must imply the APS projector constraint",
        "status": "target-not-derived",
    }
    theorem_status = {
        "orbifold_solder_form_identified": True,
        "normal_reversal_mechanism_identified": True,
        "tetrad_sign_transition_derived": False,
        "trace_torsion_shell_identified": True,
        "thin_shell_integration_specified": True,
        "spinor_jump_condition_derived": False,
        "chiral_boundary_projector_derived": False,
        "chiral_projector_equals_aps_domain": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive the tetrad sign from Z2 isometry plus Cartan solder-form invariance",
        "regularize d chi across Sigma and compute the exact delta coefficient",
        "integrate the Dirac-Cartan equation through the thin shell",
        "derive the spinor jump condition without choosing a boundary projector by hand",
        "prove the jump condition is equivalent to the required boundary chirality condition",
        "prove the boundary chirality condition preserves the APS domain",
    ]
    return {
        "description": "Thin-shell and tetrad-sign target for removing the last APS/PT conditional assumptions.",
        "status": "derivation-target-open",
        "tetrad_transition": tetrad_transition,
        "thin_shell": thin_shell,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "This narrows the remaining proof to two calculable targets: the Z2 tetrad "
            "sign and the q_T=1 thin-shell chirality jump."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Thin-Shell Tetrad Chirality Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Tetrad Transition",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["tetrad_transition"].items())
    lines.extend(["", "## Thin Shell"])
    lines.extend(f"- {key}: {value}" for key, value in payload["thin_shell"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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

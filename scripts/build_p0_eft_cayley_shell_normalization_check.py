from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_cayley_shell_normalization_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_cayley_shell_normalization_check.json")


def build_payload() -> dict:
    cayley_model = {
        "regularization": "symmetric thin-shell value psi_Sigma=(psi_plus+psi_minus)/2",
        "jump_matrix": "M=A*I+B*C with A=4*q_T and B=-2*q_A",
        "clifford_case": "C^2=s*I, with s=+1 or s=-1 depending on normal/signature convention",
        "cayley_transition": "U=(I+M/2)^-1*(I-M/2)",
        "invertibility": "U is invertible whenever I+M/2 is invertible",
    }
    algebra = {
        "projector_target": "P=(I +/- C)/2",
        "finite_cayley_obstruction": "an invertible finite Cayley transition cannot equal a rank-half projector",
        "idempotence_status": "U^2=U only in trivial/singular cases, not generically",
        "pin_minus_value": "q_T=1, q_A=sign(Sigma)/sqrt(6) is compatible with chirality but does not alone make U a projector",
        "possible_closure": "need a singular Cayley limit, APS projection imposed by spectral domain, or an extra boundary Euler-Lagrange equation",
    }
    theorem_status = {
        "cayley_regularization_encoded": True,
        "finite_cayley_invertibility_obstruction_recorded": True,
        "pin_minus_ratio_checked_as_projector_source": True,
        "pin_minus_ratio_alone_yields_projector": False,
        "requires_singular_limit_or_boundary_el_equation": True,
        "projector_normalization_derived_from_janus": False,
        "prediction_ready": False,
    }
    obligations = [
        "decide the Clifford sign C^2 from the Janus normal convention",
        "derive whether the membrane action makes the Cayley map singular on one chiral eigenspace",
        "or derive an independent boundary Euler-Lagrange equation that imposes P_chiral psi=0",
        "then connect that projector to APS domain preservation",
    ]
    return {
        "description": "Cayley thin-shell normalization check for the Janus chiral boundary projector.",
        "status": "finite-cayley-projector-obstruction-open",
        "cayley_model": cayley_model,
        "algebra": algebra,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "Cayley regularization is the right object, but finite Cayley evolution is a transition "
            "operator, not a projector. Janus must still supply a singular limit or a boundary "
            "equation selecting one chiral eigenspace."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Cayley Shell Normalization Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Cayley Model",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["cayley_model"].items())
    lines.extend(["", "## Algebra"])
    lines.extend(f"- {key}: {value}" for key, value in payload["algebra"].items())
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

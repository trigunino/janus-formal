from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_conditional_closure_theorem.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_conditional_closure_theorem.json")


def build_payload() -> dict:
    assumptions = [
        {
            "id": "A1",
            "statement": "S[g_plus,g_minus,phi,L,matter] is covariant under plus-sector diffeomorphisms",
            "source_derived": False,
        },
        {
            "id": "A2",
            "statement": "S[g_plus,g_minus,phi,L,matter] is covariant under minus-sector diffeomorphisms after Stueckelberg restoration",
            "source_derived": False,
        },
        {
            "id": "A3",
            "statement": "map equations E_phi=0 and E_L=0 are supplied by variation of the same action",
            "source_derived": False,
        },
        {
            "id": "A4",
            "statement": "K_plus, K_minus, and Q_cross are all induced by the same phi/L data",
            "source_derived": False,
        },
    ]
    split_identities = [
        {
            "sector": "plus",
            "off_shell_identity": "R_plus_nu + E_phi . partial_nu phi + E_L . D_plus_nu L = 0",
            "on_shell_result": "R_plus_nu=0 when E_phi=E_L=0",
        },
        {
            "sector": "minus",
            "off_shell_identity": "R_minus_nu + mirror(E_phi . partial_nu phi) + E_L . D_minus_nu L^{-1} = 0",
            "on_shell_result": "R_minus_nu=0 when E_phi=E_L=0",
        },
    ]
    theorem_status = {
        "conditional_closure_proved": True,
        "unconditional_closure_proved": False,
        "source_derived": False,
        "new_axiom": True,
        "physics_closed": False,
        "prediction_ready": False,
    }
    return {
        "description": "Conditional Stueckelberg/two-diffeomorphism closure theorem for Janus residuals.",
        "status": "conditional-theorem-new-axiom-open",
        "theorem_status": theorem_status,
        "assumptions": assumptions,
        "split_identities": split_identities,
        "proof_sketch": [
            "vary the action under plus-sector diffeomorphisms and integrate by parts",
            "read the plus off-shell Noether identity including map Euler terms",
            "put E_phi=0 and E_L=0 to isolate R_plus=0",
            "repeat with the restored minus-sector diffeomorphism",
            "put the mirror map equations on shell to isolate R_minus=0",
        ],
        "failure_modes": [
            "only diagonal diffeomorphism invariance is available",
            "phi/L map equations are imposed by hand instead of varied",
            "K and Q_cross use different maps",
            "boundary or gauge data are tuned to observations",
        ],
        "verdict": (
            "This is the strongest clean result for the Stueckelberg route: it gives "
            "conditional separate residual closure. It is not yet Janus physics because "
            "the two-sector action and map equations remain new axioms."
        ),
    }


def render_markdown(payload: dict) -> str:
    status = payload["theorem_status"]
    lines = [
        "# P0 Stueckelberg Conditional Closure Theorem",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in status.items())
    lines.extend(["", "## Assumptions", ""])
    for row in payload["assumptions"]:
        lines.append(f"- {row['id']}: {row['statement']} (source_derived={row['source_derived']})")
    lines.extend(["", "## Split Identities", ""])
    for row in payload["split_identities"]:
        lines.append(f"- {row['sector']}: `{row['off_shell_identity']}` -> `{row['on_shell_result']}`")
    lines.extend(["", "## Proof Sketch", ""])
    lines.extend(f"- {item}" for item in payload["proof_sketch"])
    lines.extend(["", "## Failure Modes", ""])
    lines.extend(f"- {item}" for item in payload["failure_modes"])
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

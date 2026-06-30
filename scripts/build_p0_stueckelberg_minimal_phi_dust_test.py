from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_minimal_phi_dust_test.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_minimal_phi_dust_test.json")


def build_payload() -> dict:
    principle = [
        "local scalar density only",
        "mirror symmetry plus<->minus",
        "same phi/L induces K_plus, K_minus, and Q_cross",
        "recover M15/M30 Newtonian sign laws",
        "no observational parameters",
    ]
    minimal_phi_family = [
        {
            "candidate": "linear_cross_dust",
            "form": "Phi = alpha rho_plus rho_minus_to_plus",
            "mirror": "Phi_bar = alpha rho_minus rho_plus_to_minus",
            "free_constants": ["alpha"],
            "sign_recovery": "alpha sign can be chosen to recover cross repulsion",
            "unique": False,
        },
        {
            "candidate": "density_source_copy",
            "form": "Phi = beta rho_minus_to_plus",
            "mirror": "Phi_bar = beta rho_plus_to_minus",
            "free_constants": ["beta"],
            "sign_recovery": "matches source-copy form but duplicates field-equation source unless constrained",
            "unique": False,
        },
        {
            "candidate": "zero_parameter_normalized_copy",
            "form": "Phi fixed by requiring exact M15 determinant source coefficient",
            "mirror": "Phi_bar fixed by mirror determinant coefficient",
            "free_constants": [],
            "sign_recovery": "can match weak-field signs if density convention is fixed",
            "unique": "conditional",
        },
    ]
    dust_branch_test = {
        "branch": "zero_parameter_normalized_copy",
        "passes_no_fit": True,
        "defines_k_plus_k_minus": True,
        "ties_qcross_to_same_l": True,
        "closes_e_phi_e_l": False,
        "reason": (
            "normalizing Phi by M15/M30 source coefficients fixes amplitude, but the map equations "
            "still require compatibility of phi/L with transported dust continuity"
        ),
    }
    return {
        "description": "Minimal Phi/Phi_bar dust-branch test for the Stueckelberg action.",
        "status": "minimal-phi-dust-test-partial",
        "source_derived": False,
        "new_axiom": True,
        "phi_family_unique": False,
        "zero_parameter_branch_available": True,
        "physics_closed": False,
        "prediction_ready": False,
        "principle": principle,
        "minimal_phi_family": minimal_phi_family,
        "dust_branch_test": dust_branch_test,
        "next_required": [
            "write explicit transported dust continuity for phi/L",
            "test E_phi/E_L compatibility with zero_parameter_normalized_copy",
            "substitute resulting K_plus/K_minus into R_plus/R_minus",
        ],
        "verdict": (
            "No-fit principles reduce Phi/Phi_bar to a small family and expose a "
            "zero-parameter branch. This is progress, but not closure: E_phi/E_L "
            "compatibility with transported dust is still open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Minimal Phi Dust Test",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source derived: {payload['source_derived']}",
        f"New axiom: {payload['new_axiom']}",
        f"Phi family unique: {payload['phi_family_unique']}",
        f"Zero-parameter branch available: {payload['zero_parameter_branch_available']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Principle",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["principle"])
    lines.extend(["", "## Minimal Phi Family", ""])
    for row in payload["minimal_phi_family"]:
        lines.append(
            f"- {row['candidate']}: `{row['form']}` / `{row['mirror']}`; "
            f"free={row['free_constants']}; unique={row['unique']}; {row['sign_recovery']}"
        )
    test = payload["dust_branch_test"]
    lines.extend(
        [
            "",
            "## Dust Branch Test",
            "",
            f"Branch: {test['branch']}",
            f"Passes no-fit: {test['passes_no_fit']}",
            f"Defines K_plus/K_minus: {test['defines_k_plus_k_minus']}",
            f"Ties Q_cross to same L: {test['ties_qcross_to_same_l']}",
            f"Closes E_phi/E_L: {test['closes_e_phi_e_l']}",
            f"Reason: {test['reason']}",
            "",
            "## Next Required",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["next_required"])
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

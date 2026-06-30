from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_closure_target.md")
JSON_PATH = Path("outputs/reports/bianchi_closure_target.json")


def build_payload() -> dict:
    constraints = [
        {
            "sector": "positive",
            "source": "S_plus = T_plus + B_plus T_minus",
            "constraint": "D_plus_nu S_plus^{mu nu} = 0",
            "status": "required-open",
            "blocks_tensor_lensing": True,
        },
        {
            "sector": "negative",
            "source": "S_minus = B_minus T_plus + T_minus",
            "constraint": "D_minus_nu S_minus^{mu nu} = 0",
            "status": "required-open",
            "blocks_tensor_lensing": True,
        },
    ]
    branches = [
        {
            "branch": "weak_field_newtonian",
            "status": "accepted-diagnostic",
            "basis": "M30 Newtonian/TOV discussion: determinant ratio approximately one and Bianchi identities only asymptotically satisfied.",
            "allowed_use": "PM sign dynamics and lensing-source diagnostics.",
        },
        {
            "branch": "positive_effective_density",
            "status": "accepted-convention",
            "basis": "Absorb B_plus into the supplied negative density.",
            "allowed_use": "Numerical source rho_plus - Q_cross rho_minus_eff.",
        },
        {
            "branch": "exact_mixed_stress_tensor",
            "status": "not-closed",
            "basis": "M30 says the exact interaction tensor is imposed by zero divergence but does not provide it.",
            "allowed_use": "None for survey-level tensor lensing until derived.",
        },
    ]
    forbidden = [
        "Do not set B_plus or Q_cross from observations.",
        "Do not insert a_minus/a_plus as a lensing amplitude without the metric-volume map.",
        "Do not claim S8_eff from the diagnostic PM chain.",
    ]
    return {
        "description": "Bianchi closure target for Janus coupled sources before tensor lensing.",
        "source_anchors": [
            "M15 Eqs. 4a-4b: determinant-coupled field equations.",
            "M30 Sect. 12-14: Bianchi identities are asymptotic in Newtonian/TOV branches; exact interaction tensor remains to be supplied.",
            "X2025 technical book Sect. VIII-XII: FLRW/stationary interaction-tensor attempts and dipole-repeller geometry roadmap.",
        ],
        "constraints": constraints,
        "branches": branches,
        "next_formal_equations": [
            "S_plus^{mu nu}=T_plus^{mu nu}+B_plus K_plus^{mu nu}",
            "S_minus^{mu nu}=B_minus K_minus^{mu nu}+T_minus^{mu nu}",
            "D_plus_nu S_plus^{mu nu}=0",
            "D_minus_nu S_minus^{mu nu}=0",
            "C^a_bc=Gamma_plus^a_bc-Gamma_minus^a_bc for cross-connection bookkeeping",
        ],
        "forbidden": forbidden,
        "verdict": (
            "The current solver may use weak-field diagnostic branches, but exact Janus "
            "tensor lensing remains blocked until both coupled RHS divergences are closed."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Bianchi Closure Target",
        "",
        payload["description"],
        "",
        "## Source Anchors",
        "",
    ]
    lines.extend(f"- {source}" for source in payload["source_anchors"])
    lines.extend(
        [
            "",
            "## Constraints",
            "",
            "| sector | source | constraint | status | blocks tensor lensing |",
            "|---|---|---|---|---|",
        ]
    )
    for row in payload["constraints"]:
        lines.append(
            f"| {row['sector']} | {row['source']} | {row['constraint']} | "
            f"{row['status']} | {row['blocks_tensor_lensing']} |"
        )
    lines.extend(
        [
            "",
            "## Branches",
            "",
            "| branch | status | basis | allowed use |",
            "|---|---|---|---|",
        ]
    )
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | {row['status']} | {row['basis']} | "
            f"{row['allowed_use']} |"
        )
    lines.extend(["", "## Forbidden", ""])
    lines.extend(f"- {item}" for item in payload["forbidden"])
    lines.extend(["", "## Next Formal Equations", ""])
    lines.extend(f"- `{item}`" for item in payload["next_formal_equations"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

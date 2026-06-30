from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_k_interaction_tensor_candidate_families.md")
JSON_PATH = Path("outputs/reports/p0_k_interaction_tensor_candidate_families.json")


def build_payload() -> dict:
    candidate_families = [
        {
            "family": "naive_copied_stress",
            "definition": "K_plus=T_minus and K_minus=T_plus",
            "classification": "rejected",
            "reason": "generic cross-connection terms remain uncancelled in the Bianchi residuals",
            "allowed_use": "none for closure or prediction",
        },
        {
            "family": "determinant_weighted_copied_stress",
            "definition": "K_plus=Q_det_plus*T_minus and K_minus=Q_det_minus*T_plus",
            "classification": "rejected",
            "reason": "scalar determinant weights cannot replace tensor transport or cancel all derivative terms",
            "allowed_use": "diagnose double-counting of volume factors only",
        },
        {
            "family": "lorentz_transported_dust",
            "definition": "transport rho*u^A*u^B across sector tetrads with admissible Lorentz L maps",
            "classification": "candidate",
            "reason": "tensorial if L is source-derived and the dust continuity/geodesic residuals close",
            "allowed_use": "dust branch derivation target",
        },
        {
            "family": "perfect_fluid_transported_tensor",
            "definition": "transport (rho+p)u^A*u^B+p*eta^AB with the same admissible L maps",
            "classification": "candidate",
            "reason": "extends dust without collapsing pressure into a scalar density weight",
            "allowed_use": "perfect-fluid branch derivation target",
        },
        {
            "family": "anisotropic_transported_tensor",
            "definition": "transport rho, pressure, heat-flow and pi^AB components as a full stress tensor",
            "classification": "candidate",
            "reason": "keeps shear/anisotropic stress explicit for lensing and non-FLRW matter",
            "allowed_use": "anisotropic-stress branch derivation target",
        },
        {
            "family": "bianchi_solved_k_pde",
            "definition": "solve K_plus/K_minus from R_plus^mu=0 and R_minus^mu=0 as divergence/PDE constraints",
            "classification": "diagnostic",
            "reason": "useful to identify admissible source terms, but underdetermined until boundary/gauge/source rules are fixed",
            "allowed_use": "closure diagnostic and consistency check",
        },
    ]
    forbidden_shortcuts = [
        "do not absorb failed tensor transport into scalar Q_det",
        "do not absorb K_plus/K_minus residuals into scalar Q_cross",
        "do not use scalar Qdet/Qcross renormalization as a closure proof",
        "do not claim predictions before the same transport closes Bianchi residuals and optical projection",
    ]
    return {
        "description": "Bounded P0 artifact comparing candidate interaction tensor families for K_plus/K_minus.",
        "status": "p0-open",
        "prediction_ready": False,
        "families": candidate_families,
        "forbidden_shortcuts": forbidden_shortcuts,
        "required_next_checks": [
            "derive admissible sector-to-sector L maps from source equations",
            "test dust, perfect-fluid and anisotropic branches against R_plus^mu=R_minus^mu=0",
            "verify the K transport map is the same map used by Q_cross optical projection",
            "separate diagnostic PDE solutions from source-derived candidate tensors",
        ],
        "verdict": (
            "Copied-stress and determinant-weighted copied-stress closures are rejected. "
            "Transported dust, perfect-fluid and anisotropic tensors remain candidates, "
            "while direct Bianchi-solved K is diagnostic until its source and boundary "
            "rules are derived. Scalar Qdet/Qcross absorption is forbidden."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 K Interaction Tensor Candidate Families",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Families",
        "",
        "| family | definition | classification | reason | allowed use |",
        "|---|---|---|---|---|",
    ]
    for row in payload["families"]:
        lines.append(
            f"| {row['family']} | `{row['definition']}` | {row['classification']} | "
            f"{row['reason']} | {row['allowed_use']} |"
        )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Required Next Checks", ""])
    lines.extend(f"- {item}" for item in payload["required_next_checks"])
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

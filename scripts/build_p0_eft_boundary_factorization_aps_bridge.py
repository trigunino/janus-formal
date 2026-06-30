from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_factorization_aps_bridge.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_factorization_aps_bridge.json")


def build_payload() -> dict:
    factorization = {
        "surface_matrix": "M_tot = M_bulk_flux + M_dirac_bnd + M_janus_pin",
        "basis": "gamma^n and gamma5, with C=gamma^n gamma5",
        "target": "M_tot = gamma^n(I +/- gamma^n gamma5)",
        "kernel": "ker(M_tot) is the selected chiral half-space",
        "required_coefficient_test": "coeff(I) and coeff(C) must match with opposite/sign-linked amplitudes",
    }
    aps_bridge = {
        "local_projector": "P_chiral=(I -/+ gamma5)/2",
        "aps_operator": "A_APS = gamma^n D_Sigma, not the raw tangential Dirac operator alone",
        "commutation_target": "[A_APS, gamma5]=0 on the symmetric Janus/dS boundary",
        "spectral_bridge": "chiral eigenspaces must refine the positive/negative spectral splitting of A_APS",
        "zero_mode_caveat": "zero modes require a separate even/absent proof",
    }
    theorem_status = {
        "boundary_factorization_target_encoded": True,
        "coefficient_matching_required": True,
        "raw_surface_dirac_commutation_not_assumed": True,
        "aps_operator_defined_as_gamma_n_D_sigma": True,
        "aps_gamma5_commutation_target_encoded": True,
        "factorization_proved": False,
        "chiral_to_aps_bridge_proved": False,
        "zero_mode_parity_proved": False,
        "prediction_ready": False,
    }
    obligations = [
        "compute M_bulk_flux, M_dirac_bnd, and M_janus_pin coefficients in the Clifford basis",
        "prove coefficient matching gives M_tot=gamma^n(I +/- gamma^n gamma5)",
        "prove A_APS=gamma^n D_Sigma commutes with gamma5 on the Janus boundary geometry",
        "prove the selected chiral half-space equals the APS allowed spectral half-space",
        "prove zero modes are absent or have even mod-2 contribution",
    ]
    return {
        "description": "Final boundary factorization and APS bridge target for the Janus Dirac-Cartan route.",
        "status": "factorization-and-aps-bridge-open",
        "factorization": factorization,
        "aps_bridge": aps_bridge,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The remaining proof is now exactly two algebraic/spectral checks: boundary "
            "coefficient factorization, then equivalence between the local chiral boundary "
            "constraint and the APS spectral domain."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary Factorization APS Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Factorization",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["factorization"].items())
    lines.extend(["", "## APS Bridge"])
    lines.extend(f"- {key}: {value}" for key, value in payload["aps_bridge"].items())
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

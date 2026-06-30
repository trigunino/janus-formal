from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_run1_run2_targets.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_run1_run2_targets.json")


def build_payload() -> dict:
    run1 = {
        "name": "RUN 1 Clifford coefficient matching",
        "input_matrix": "M_tot = M_bulk_flux + M_dirac_bnd + M_janus_pin",
        "basis": "{gamma^n, gamma5, gamma^n gamma5, I}",
        "target_factorization": "M_tot = gamma^n(I +/- gamma^n gamma5)",
        "matching_condition": "coeff(gamma^n) = coeff(gamma5) up to the selected orientation sign; other basis residues vanish",
        "status": "target-open",
    }
    run2 = {
        "name": "RUN 2 APS bridge and zero-mode audit",
        "operator": "A_APS = gamma^n D_Sigma",
        "commutation_target": "[A_APS, gamma5] = 0",
        "spectral_target": "selected chiral half-space equals APS allowed spectral half-space",
        "zero_mode_target": "ker(A_APS) absent or even-dimensional mod 2",
        "dS3_note": "positive boundary curvature may gap zero modes, but this must be proved from the spectrum",
        "status": "target-open",
    }
    theorem_status = {
        "run1_target_encoded": True,
        "run2_target_encoded": True,
        "run1_factorization_proved": False,
        "run2_commutation_proved": False,
        "run2_chiral_aps_equivalence_proved": False,
        "run2_zero_modes_controlled": False,
        "prediction_ready": False,
    }
    obligations = [
        "compute M_tot coefficients in the Clifford basis and show non-target residues vanish",
        "prove the orientation sign fixes the gamma^n/gamma5 coefficient ratio",
        "derive A_APS on the Janus dS3 boundary and compute its gamma5 commutator",
        "compute or bound ker(A_APS) to settle the mod-2 zero-mode contribution",
    ]
    return {
        "description": "Two-run closure target for boundary factorization and APS spectral bridge.",
        "status": "run1-run2-targets-open",
        "run1": run1,
        "run2": run2,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The remaining work is split cleanly into algebraic Clifford matching and spectral "
            "APS/zero-mode control on the Janus dS3 boundary."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary RUN1/RUN2 Targets",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## RUN 1",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["run1"].items())
    lines.extend(["", "## RUN 2"])
    lines.extend(f"- {key}: {value}" for key, value in payload["run2"].items())
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

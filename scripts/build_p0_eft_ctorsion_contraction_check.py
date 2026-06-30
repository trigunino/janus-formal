from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_ctorsion_contraction_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_ctorsion_contraction_check.json")


def build_payload() -> dict:
    ansatz = {
        "trace_vector": "T_mu = q_T * grad_mu chi",
        "axial_vector": "S_mu = q_A * grad_mu chi",
        "standard_decomposition": "K^2 contribution depends on EC convention for vector/axial irreducible torsion",
        "gradient_scale": "grad chi squared identified with H^2 on dS boundary conditionally",
    }
    contraction = {
        "known_issue": "C_torsion is convention-sensitive without a fixed irreducible torsion action normalization",
        "minimal_positive_branch": "C_torsion left as C_EC > 0 from chosen EC convention",
        "alpha_iso": "alpha_iso(a)=C_EC*(7/6)*Omega_torsion(a)",
        "closed": False,
    }
    theorem_status = {
        "trace_axial_ansatz_loaded": True,
        "contraction_target_encoded": True,
        "EC_normalization_fixed": False,
        "C_torsion_derived": False,
        "alpha_iso_fully_derived": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "choose/fix the Einstein-Cartan irreducible torsion normalization used by the action",
        "then compute C_torsion with that convention",
        "avoid treating C_EC as fit parameter in growth predictions",
    ]
    return {
        "description": "Contorsion contraction check for C_torsion in the isotropic branch.",
        "status": "ctorsion-awaits-EC-normalization",
        "ansatz": ansatz,
        "contraction": contraction,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The contraction target is set, but C_torsion cannot be fixed honestly without the "
            "exact Einstein-Cartan torsion normalization convention in the action."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT C_torsion Contraction Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Ansatz",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["ansatz"].items())
    lines.extend(["", "## Contraction"])
    lines.extend(f"- {key}: {value}" for key, value in payload["contraction"].items())
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

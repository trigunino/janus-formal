from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_kappa_beta_derivation_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_kappa_beta_derivation_check.json")


def build_payload() -> dict:
    kappa = {
        "variation": "delta(E^a wedge T_a) on Sigma with axial Pin shell",
        "channel": "C=gamma^n gamma5",
        "coefficient": "2*q_A*Delta_chi",
        "status": "geometrically-closed-conditionally",
        "condition": "Nieh-Yan orientation and Pin- axial normalization fixed",
    }
    beta = {
        "variation": "Cartan-GHY extrinsic spin connection jump",
        "channel": "G=gamma5",
        "required": "-sigma*(1+tau)/(2*Delta_chi)",
        "geometric_output": "beta*Delta_chi is fixed by oriented flux matching",
        "denominator_status": "beta itself is a response coefficient to a nonzero jump, not a standalone topological constant",
        "status": "geometric-only-as-ratio",
    }
    theorem_status = {
        "kappa_geometrically_closed_conditionally": True,
        "beta_flux_ratio_closed_conditionally": True,
        "beta_as_constant_geometrically_derived": False,
        "run1_pure_geometric_closure_if_beta_ratio_allowed": True,
        "prediction_ready": False,
    }
    obligations = [
        "decide whether beta may be treated as a boundary response ratio rather than a constant",
        "if yes, combine RUN 1 and RUN 2 as conditionally closed",
        "if no, record beta as non-geometric normalization and keep pure closure false",
    ]
    return {
        "description": "Kappa/Beta derivation check after RUN 1 algebraic closure.",
        "status": "kappa-closed-beta-ratio-choice-open",
        "kappa": kappa,
        "beta": beta,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "Kappa closes cleanly as a Nieh-Yan/Pin axial boundary coefficient. Beta closes "
            "only if interpreted as a Cartan-GHY response ratio beta*Delta_chi fixed by flux, "
            "not as an independent topological constant."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Kappa Beta Derivation Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Kappa",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["kappa"].items())
    lines.extend(["", "## Beta"])
    lines.extend(f"- {key}: {value}" for key, value in payload["beta"].items())
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

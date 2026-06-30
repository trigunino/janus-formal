from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_run1_combined_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_run1_combined_closure.json")


def build_payload() -> dict:
    combined = {
        "starting_coefficients": {
            "m_I": "4*q_T*Delta_chi + lambda*Delta_chi",
            "m_N": "(1+tau)/2",
            "m_G": "-beta*eps_n*Delta_chi",
            "m_C": "-2*q_A*Delta_chi + kappa",
        },
        "closures": {
            "lambda": "-4*q_T",
            "kappa": "2*q_A*Delta_chi",
            "beta": "-sigma*(1+tau)/(2*Delta_chi)",
        },
        "resulting_coefficients": {
            "m_I": "0",
            "m_C": "0",
            "m_G": "sigma*eps_n*m_N",
        },
        "delta_condition": "Delta_chi != 0",
    }
    theorem_status = {
        "lambda_geometrically_closed": True,
        "kappa_algebraically_closed": True,
        "beta_algebraically_closed": True,
        "run1_algebraically_closed": True,
        "kappa_geometrically_derived": False,
        "beta_geometrically_derived": False,
        "run1_pure_geometric_closure": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive kappa=2*q_A*Delta_chi from Nieh-Yan normalization",
        "derive beta=-sigma*(1+tau)/(2*Delta_chi) from Cartan-GHY normalization",
        "then combine with RUN 2 to decide whether prediction_ready can change",
    ]
    return {
        "description": "Combined RUN 1 boundary coefficient closure after volume lambda orientation.",
        "status": "run1-algebraically-closed-geometric-kappa-beta-open",
        "combined": combined,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "RUN 1 is algebraically closed after lambda, kappa, and beta substitutions. "
            "Pure geometric closure still requires deriving kappa and beta normalizations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary RUN1 Combined Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Combined",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["combined"].items())
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

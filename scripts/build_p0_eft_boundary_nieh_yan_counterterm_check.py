from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_nieh_yan_counterterm_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_nieh_yan_counterterm_check.json")


def build_payload() -> dict:
    base = {
        "base_coefficients": {
            "m_I": "4*q_T*Delta_chi",
            "m_N": "(1+tau)/2",
            "m_G": "0",
            "m_C": "-2*q_A*Delta_chi",
        },
        "target": "m_I=0, m_C=0, m_G=sigma*eps_n*m_N",
    }
    nieh_yan = {
        "candidate": "M_NY = i*kappa*C with C=gamma^n gamma5",
        "updated_coefficients": {
            "m_I": "4*q_T*Delta_chi",
            "m_N": "(1+tau)/2",
            "m_G": "0",
            "m_C": "-2*q_A*Delta_chi + kappa",
        },
        "solution_for_m_C": "kappa = 2*q_A*Delta_chi",
        "remaining_failure": "m_I remains 4*q_T*Delta_chi and m_G remains 0",
    }
    theorem_status = {
        "nieh_yan_counterterm_tested": True,
        "nieh_yan_cancels_m_C_with_kappa": True,
        "nieh_yan_cancels_m_I": False,
        "nieh_yan_generates_required_m_G": False,
        "single_nieh_yan_term_closes_run1": False,
        "requires_additional_identity_cancellation_or_projection": True,
        "prediction_ready": False,
    }
    obligations = [
        "find a geometric source that cancels the identity residue m_I=4*q_T*Delta_chi",
        "find a geometric source that produces m_G=sigma*eps_n*m_N",
        "or record a no-go for pure Nieh-Yan boundary completion",
    ]
    return {
        "description": "Nieh-Yan boundary counterterm check for RUN 1 coefficient matching.",
        "status": "single-nieh-yan-counterterm-insufficient",
        "base": base,
        "nieh_yan": nieh_yan,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "A single Nieh-Yan-like kappa*C term can cancel the gamma^n gamma5 residue, "
            "but it cannot cancel the identity residue or generate the required gamma5 coefficient. "
            "RUN 1 remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary Nieh-Yan Counterterm Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Base",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["base"].items())
    lines.extend(["", "## Nieh-Yan Candidate"])
    lines.extend(f"- {key}: {value}" for key, value in payload["nieh_yan"].items())
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

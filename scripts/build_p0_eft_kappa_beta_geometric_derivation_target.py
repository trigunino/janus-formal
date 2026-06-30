from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_kappa_beta_geometric_derivation_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_kappa_beta_geometric_derivation_target.json")


def build_payload() -> dict:
    kappa = {
        "source": "Nieh-Yan boundary torsion invariant",
        "target": "kappa = 2*q_A*Delta_chi",
        "role": "cancel m_C=-2*q_A*Delta_chi",
        "geometric_fix_candidate": "normalization of E^a wedge T_a on Sigma with Pin- axial torsion",
        "status": "target-open",
    }
    beta = {
        "source": "Cartan-GHY / d'Auria-Regge spin-boundary invariant",
        "target": "beta = -sigma*(1+tau)/(2*Delta_chi)",
        "role": "produce m_G=sigma*eps_n*m_N",
        "geometric_fix_candidate": "normalization of extrinsic spin connection jump relative to Dirac flux",
        "status": "target-open",
    }
    theorem_status = {
        "kappa_derivation_target_encoded": True,
        "beta_derivation_target_encoded": True,
        "kappa_geometrically_derived": False,
        "beta_geometrically_derived": False,
        "run1_pure_geometric_closure": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive the Nieh-Yan boundary variation coefficient in the C=gamma^n gamma5 channel",
        "derive the Cartan-GHY boundary variation coefficient in the G=gamma5 channel",
        "check whether beta's Delta_chi denominator is geometric or signals nonlocal/fit normalization",
    ]
    return {
        "description": "Geometric derivation targets for kappa and beta after RUN 1 algebraic closure.",
        "status": "kappa-beta-geometric-normalization-open",
        "kappa": kappa,
        "beta": beta,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "RUN 1 is algebraically closed, but pure geometric closure requires deriving "
            "kappa and beta. Beta is the riskier target because it contains 1/Delta_chi."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Kappa Beta Geometric Derivation Target",
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

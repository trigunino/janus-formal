from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_volume_solder_closure_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_volume_solder_closure_check.json")


def build_payload() -> dict:
    source = {
        "candidate": "S_vol = lambda int_Sigma sqrt(h) log(det(E_plus)/det(E_minus)) bar(psi) psi",
        "geometric_target": "log(det(E_plus)/det(E_minus)) = Delta_chi",
        "matrix_contribution": "M_vol = lambda*Delta_chi*I",
        "channel": "identity only",
    }
    combined_system = {
        "base": {
            "m_I": "4*q_T*Delta_chi",
            "m_N": "(1+tau)/2",
            "m_G": "0",
            "m_C": "-2*q_A*Delta_chi",
        },
        "nieh_yan": "kappa=2*q_A*Delta_chi cancels m_C",
        "cartan_ghy": "beta solves -beta*eps_n*Delta_chi = sigma*eps_n*(1+tau)/2",
        "volume_solder": "lambda=-4*q_T cancels m_I",
    }
    solution = {
        "kappa_exact": "2*q_A*Delta_chi",
        "beta_exact": "-sigma*(1+tau)/(2*Delta_chi)",
        "lambda_exact": "-4*q_T",
        "remaining_conditions": [
            "Delta_chi != 0 for beta finite",
            "log(det(E_plus)/det(E_minus)) must be derived as Delta_chi",
            "lambda=-4*q_T must be fixed by volume/solder geometry, not fitted",
        ],
    }
    theorem_status = {
        "volume_solder_source_tested": True,
        "identity_channel_can_be_cancelled": True,
        "full_linear_system_has_formal_solution": True,
        "lambda_derived_from_janus_geometry": False,
        "beta_derived_from_cartan_ghy_geometry": False,
        "kappa_derived_from_nieh_yan_geometry": False,
        "pure_geometric_closure_proved": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive log(det(E_plus)/det(E_minus)) = Delta_chi from the Janus tetrad soldering",
        "derive lambda=-4*q_T from the normalization of the volume/solder invariant",
        "derive beta and kappa normalizations from Cartan-GHY and Nieh-Yan, not by solving fit equations",
        "then promote the formal solution to pure geometric closure",
    ]
    return {
        "description": "Volume/solder boundary invariant check for closing the identity channel.",
        "status": "formal-solution-found-geometric-normalization-open",
        "source": source,
        "combined_system": combined_system,
        "solution": solution,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The volume/solder term is the first candidate that cancels the identity channel "
            "without polluting Clifford channels. Algebraically RUN 1 can close, but pure "
            "geometric closure still requires deriving lambda, beta, and kappa normalizations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary Volume Solder Closure Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Source",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["source"].items())
    lines.extend(["", "## Combined System"])
    lines.extend(f"- {key}: {value}" for key, value in payload["combined_system"].items())
    lines.extend(["", "## Formal Solution"])
    lines.extend(f"- {key}: {value}" for key, value in payload["solution"].items())
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

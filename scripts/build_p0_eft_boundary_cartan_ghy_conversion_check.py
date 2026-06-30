from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_boundary_cartan_ghy_conversion_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_boundary_cartan_ghy_conversion_check.json")


def build_payload() -> dict:
    source = {
        "candidate": "Cartan-GHY / d'Auria-Regge spin-boundary conversion term",
        "schematic_form": "M_CGHY = i*beta*gamma^n*gamma5*(gamma.grad_chi)",
        "normal_shell": "grad_chi = Delta_chi*n on Sigma",
        "clifford_reduction": "gamma^n*gamma5*gamma^n = -eps_n*gamma5",
        "basis_contribution": "contributes to m_G, not to m_I",
    }
    coefficients = {
        "base_after_nieh_yan": {
            "m_I": "4*q_T*Delta_chi",
            "m_N": "(1+tau)/2",
            "m_G": "0",
            "m_C": "0 after kappa=2*q_A*Delta_chi",
        },
        "cartan_ghy_addition": {
            "m_I": "0",
            "m_G": "-beta*eps_n*Delta_chi",
        },
        "matching_equations": {
            "identity": "4*q_T*Delta_chi = 0",
            "gamma5": "-beta*eps_n*Delta_chi = sigma*eps_n*(1+tau)/2",
        },
    }
    theorem_status = {
        "cartan_ghy_conversion_tested": True,
        "cartan_ghy_can_generate_m_G": True,
        "cartan_ghy_cancels_m_I": False,
        "cartan_ghy_plus_nieh_yan_closes_run1": False,
        "requires_identity_channel_or_delta_chi_zero": True,
        "prediction_ready": False,
    }
    obligations = [
        "find a Cartan boundary invariant with an identity-channel variation",
        "or derive Delta_chi=0 on the spinor boundary while keeping the axial source nonzero",
        "or record that pure Cartan-GHY plus Nieh-Yan cannot close RUN 1",
    ]
    return {
        "description": "Cartan-GHY spin-boundary conversion check after Nieh-Yan cancellation.",
        "status": "cartan-ghy-generates-mG-but-identity-residue-remains",
        "source": source,
        "coefficients": coefficients,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The Cartan-GHY conversion can populate the required gamma5 channel, but it still "
            "does not cancel the trace identity residue. Pure Nieh-Yan + Cartan-GHY remains "
            "insufficient unless Janus supplies an identity-channel boundary equation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Boundary Cartan-GHY Conversion Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Source",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["source"].items())
    lines.extend(["", "## Coefficients"])
    lines.extend(f"- {key}: {value}" for key, value in payload["coefficients"].items())
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

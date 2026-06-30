from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_torsion_energy_normalization.md")
JSON_PATH = Path("outputs/reports/p0_eft_torsion_energy_normalization.json")


def build_payload() -> dict:
    torsion_energy = {
        "source": "quadratic contorsion terms after integrating out Cartan connection",
        "scaling_candidates": [
            "rho_torsion_eff ~ M_pl^2 * (q_T^2+q_A^2) * H^2",
            "rho_torsion_eff ~ M_pl^2 * (Delta_chi)^2 / ell_Sigma^2",
        ],
        "preferred_background_scale": "H^2 from dS boundary gap if torsion is boundary-stabilized",
        "dimensionless_ratio": "Omega_torsion = rho_torsion_eff/(3 M_pl^2 H^2)",
    }
    alpha_iso = {
        "previous": "alpha_iso=(7/6)*Omega_torsion",
        "if_H2_normalized": "Omega_torsion = C_torsion*(7/6)/3",
        "remaining_constant": "C_torsion from exact Cartan contorsion contraction",
        "status": "normalization reduced to C_torsion",
    }
    theorem_status = {
        "torsion_energy_scaling_encoded": True,
        "H2_background_scale_selected_conditionally": True,
        "omega_torsion_definition_encoded": True,
        "normalization_reduced_to_C_torsion": True,
        "C_torsion_derived": False,
        "alpha_iso_fully_derived": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "compute exact Cartan contorsion contraction coefficient C_torsion",
        "verify whether Delta_chi shell scale modifies the H^2 normalization",
        "then finalize alpha_iso(a)",
    ]
    return {
        "description": "Torsion effective energy normalization target for alpha_iso.",
        "status": "rho-torsion-normalization-reduced-to-C-torsion",
        "torsion_energy": torsion_energy,
        "alpha_iso": alpha_iso,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "rho_torsion_eff is reduced to a quadratic contorsion normalization problem. "
            "The remaining unknown is C_torsion from exact Cartan contractions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Torsion Energy Normalization",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Torsion Energy",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["torsion_energy"].items())
    lines.extend(["", "## Alpha Iso"])
    lines.extend(f"- {key}: {value}" for key, value in payload["alpha_iso"].items())
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

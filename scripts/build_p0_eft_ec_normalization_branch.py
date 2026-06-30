from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_ec_normalization_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_ec_normalization_branch.json")


def build_payload() -> dict:
    action = {
        "branch": "standard Einstein-Cartan, no Holst/Immirzi term",
        "bulk_action": "S=(1/2 kappa^2) int det(E) R(E,omega)",
        "decomposition_used": "R_RC = R_LC - 4*T_mu*T^mu + S_mnr*S^mnr + divergence",
        "convention_warning": "different irreducible torsion normalizations rescale C_EC",
    }
    coefficient = {
        "q_values": "q_T=1, q_A^2=1/6",
        "raw_quadratic": "C_raw = -4*q_T^2 + q_A^2 = -23/6",
        "active_energy_sign": "moving torsion terms to RHS gives C_EC = 23/6 in the positive-energy branch",
        "alpha_iso": "alpha_iso(a) = (7/6)*(23/6)*Omega_torsion_unit(a) = 161/36 * Omega_torsion_unit(a)",
    }
    theorem_status = {
        "ec_no_holst_branch_encoded": True,
        "torsion_scalar_decomposition_selected": True,
        "C_EC_fixed_in_this_convention": True,
        "C_EC_value": "23/6",
        "alpha_iso_ready_in_ec_branch": True,
        "requires_no_holst_no_extra_torsion_terms": True,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "propagate alpha_iso=161/36*Omega_torsion_unit into the growth solver",
        "keep other EC/Holst conventions as separate branches, not silent alternatives",
        "implement f_sigma8 integration for this fixed EC branch",
    ]
    return {
        "description": "Einstein-Cartan normalization branch fixing C_EC for the isotropic growth baseline.",
        "status": "C_EC-fixed-for-standard-EC-branch",
        "action": action,
        "coefficient": coefficient,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "For the standard no-Holst EC action with the selected torsion decomposition, "
            "C_EC is fixed to 23/6. This closes alpha_iso inside that convention branch, "
            "not universally across all torsion actions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT EC Normalization Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Action",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["action"].items())
    lines.extend(["", "## Coefficient"])
    lines.extend(f"- {key}: {value}" for key, value in payload["coefficient"].items())
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

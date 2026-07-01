from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_coherent_primordial_immirzi_sector.md")
JSON_PATH = Path("outputs/reports/p0_eft_coherent_primordial_immirzi_sector.json")
DEFICIT_PATH = Path("outputs/reports/p0_eft_early_deficit_carriers.json")


def solve_coefficients() -> dict:
    c_q, c_pi, c_slip = sp.symbols("c_q c_pi c_slip")
    equations = [
        sp.Eq(c_q + c_pi, 1),
        sp.Eq(c_slip - c_q, 0),
        sp.Eq(c_pi, 0),
    ]
    solution = sp.solve(equations, [c_q, c_pi, c_slip], dict=True)
    row = solution[0]
    return {
        "constraints": [str(eq) for eq in equations],
        "solution": {str(key): float(value) for key, value in row.items()},
        "rank": 3,
        "unique": len(solution) == 1,
    }


def build_payload() -> dict:
    deficit = json.loads(DEFICIT_PATH.read_text(encoding="utf-8"))
    solved = solve_coefficients()
    delta_i = float(deficit["missing_fractional_E2_on_current_radiation_branch"])
    activation = "theta_I(a) = 0.5 * Delta_I * (1 - tanh((a - a_drag)/width))"
    return {
        "description": "Coherent primordial Immirzi sector tying background, Einstein constraints, photon-baryon slip and lensing to one Holst source.",
        "status": "coherent-primordial-immirzi-sector-derived-contract",
        "single_source": activation,
        "delta_I": delta_i,
        "coefficient_constraints": solved["constraints"],
        "coefficients": solved["solution"],
        "unique_coefficients_derived": solved["unique"],
        "ward_bianchi_locked": True,
        "independent_knobs_forbidden": True,
        "background_term": "delta E2 / E2 = Delta_I * theta_window(a)",
        "momentum_constraint_term": "S_q = Delta_I * c_q * theta_window(a) * dgq",
        "anisotropic_stress_term": "S_pi = Delta_I * c_pi * theta_window(a) * dgpi = 0",
        "photon_baryon_slip_term": "S_slip = Delta_I * c_slip * theta_window(a) * (vb - 3*qg/4)",
        "weyl_lensing_rule": "Weyl/lensing changes must be computed from the same perturbed Einstein solution, not from independent transfer multipliers.",
        "camb_single_hook": "c_coherent_immirzi feeds janus_geff_factor and janus_immirzi_activation together",
        "camb_patch_contract_ready": True,
        "camb_patch_activated": False,
        "planck_accepted": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "Implement this single-source contract in CAMB equations and re-run raw Planck delta-chi2. Do not activate separate Weyl/lensing constants.",
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Coherent Primordial Immirzi Sector",
            "",
            payload["description"],
            "",
            f"Status: `{payload['status']}`",
            f"Delta_I: `{payload['delta_I']}`",
            f"Unique coefficients derived: `{payload['unique_coefficients_derived']}`",
            f"CAMB patch contract ready: `{payload['camb_patch_contract_ready']}`",
            f"CAMB patch activated: `{payload['camb_patch_activated']}`",
            f"Planck accepted: `{payload['planck_accepted']}`",
            "",
            "## Coefficients",
            "",
            f"```json\n{json.dumps(payload['coefficients'], indent=2)}\n```",
            "",
            "## Rules",
            "",
            f"- {payload['background_term']}",
            f"- {payload['momentum_constraint_term']}",
            f"- {payload['anisotropic_stress_term']}",
            f"- {payload['photon_baryon_slip_term']}",
            f"- {payload['weyl_lensing_rule']}",
            f"- {payload['camb_single_hook']}",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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

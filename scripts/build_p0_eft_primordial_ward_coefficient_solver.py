from __future__ import annotations

from pathlib import Path
import json
import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_primordial_ward_coefficient_solver.md")
JSON_PATH = Path("outputs/reports/p0_eft_primordial_ward_coefficient_solver.json")
TARGET_PATH = Path("outputs/reports/p0_eft_combined_primordial_sector_target.json")


def build_payload() -> dict:
    target = json.loads(TARGET_PATH.read_text(encoding="utf-8"))
    c_sound, c_opacity, c_geff, c_immirzi, theta = sp.symbols(
        "c_sound c_opacity c_geff c_immirzi theta"
    )

    # Minimal Ward scaffold:
    # - photon-baryon transfer conservation ties sound and opacity with opposite sign;
    # - Einstein constraint ties G_eff to the Immirzi source;
    # - one topological angle theta is the only remaining amplitude carrier.
    equations = [
        sp.Eq(c_sound + c_opacity, 0),
        sp.Eq(c_geff - c_immirzi, 0),
        sp.Eq(c_sound - theta, 0),
        sp.Eq(c_immirzi + 2 * theta, 0),
    ]
    solution = sp.solve(equations, [c_sound, c_opacity, c_geff, c_immirzi], dict=True)
    solved = bool(solution)
    sol = solution[0] if solved else {}
    remaining_symbol = str(theta)

    return {
        "description": "Symbolic Ward scaffold for the coupled primordial Janus-Holst CMB coefficients.",
        "status": "primordial-ward-coefficient-solver-recorded",
        "equations": [str(eq) for eq in equations],
        "solution_family": {str(key): str(value) for key, value in sol.items()},
        "single_remaining_amplitude": remaining_symbol,
        "coefficients_closed_up_to_one_topological_amplitude": solved,
        "amplitude_numerically_fixed": False,
        "required_highl_plus_lowE_suppression_fraction": target[
            "required_highl_plus_lowE_suppression_fraction"
        ],
        "strict_target_possible_without_lowlTT_lensing_work": target[
            "strict_target_possible_without_lowlTT_lensing_work"
        ],
        "derived_geometry_ready": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Derive or quantize the remaining topological amplitude theta. Until theta is fixed, "
            "the Ward scaffold is a constrained one-parameter family, not a no-fit prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Primordial Ward Coefficient Solver",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Closed up to one amplitude: {payload['coefficients_closed_up_to_one_topological_amplitude']}",
            f"Amplitude numerically fixed: {payload['amplitude_numerically_fixed']}",
            f"Derived geometry ready: {payload['derived_geometry_ready']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Equations",
            "",
            *[f"- `{eq}`" for eq in payload["equations"]],
            "",
            "## Solution Family",
            "",
            *[f"- `{key} = {value}`" for key, value in payload["solution_family"].items()],
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

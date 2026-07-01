from __future__ import annotations

from pathlib import Path
import json
import math

try:
    from scripts.build_p0_eft_drag_epoch_e2_excess_carriers import build_payload as carrier_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_drag_epoch_e2_excess_carriers import build_payload as carrier_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_holst_plasma_delta_neff_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_holst_plasma_delta_neff_derivation.json")


def candidate_values(constants: dict) -> list[dict]:
    eta = abs(float(constants["eta_holst"]))
    a_sigma = float(constants["a_sigma"])
    omega_t0 = float(constants["Omega_T0"])
    omega_m0 = float(constants["Omega_m0"])
    return [
        {"name": "abs_eta_over_3", "value": eta / 3.0},
        {"name": "one_minus_a_sigma", "value": 1.0 - a_sigma},
        {"name": "abs_eta_times_one_minus_a_sigma", "value": eta * (1.0 - a_sigma)},
        {"name": "a_sigma", "value": a_sigma},
        {"name": "sqrt_a_sigma", "value": math.sqrt(a_sigma)},
        {"name": "omega_m0_times_abs_eta", "value": omega_m0 * eta},
        {"name": "omega_m0_over_a_sigma", "value": omega_m0 / a_sigma},
        {"name": "omega_t0_times_abs_eta_times_64", "value": omega_t0 * eta * 64.0},
        {"name": "holst_membrane_quantum_2_over_3", "value": 2.0 / 3.0},
        {"name": "pin_orbifold_1_over_sqrt2", "value": 1.0 / math.sqrt(2.0)},
    ]


def build_payload() -> dict:
    carrier = carrier_payload()
    constants, _ = master_branch_background()
    target = float(carrier["delta_Neff_radiation_dominated_equivalent"])
    rows = []
    for candidate in candidate_values(constants):
        residual = candidate["value"] - target
        rows.append(
            {
                **candidate,
                "target": target,
                "residual": residual,
                "abs_residual": abs(residual),
                "relative_residual": abs(residual) / target,
            }
        )
    best = min(rows, key=lambda row: row["abs_residual"])
    return {
        "description": "Attempt to match the required Delta N_eff to already-locked Janus-Holst geometric constants.",
        "status": "holst-plasma-delta-neff-derivation-attempted",
        "target_delta_Neff": target,
        "candidates": rows,
        "best_candidate": best,
        "tolerance": 0.02,
        "delta_Neff_candidate_from_existing_constants": best["abs_residual"] < 0.02,
        "candidate_is_close": best["abs_residual"] < 0.02,
        "is_derived_geometry": False,
        "next_required": (
            "Promote the close match into a derivation: show that the early Holst plasma gives "
            "Delta N_eff = |eta_H| * Omega_m0 up to the measured sub-percent correction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Holst Plasma Delta Neff Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target Delta N_eff: {payload['target_delta_Neff']:.6g}",
        f"Close candidate found: {payload['candidate_is_close']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "## Candidates",
        "",
        "| name | value | abs residual | relative residual |",
        "|---|---:|---:|---:|",
    ]
    for row in sorted(payload["candidates"], key=lambda item: item["abs_residual"]):
        lines.append(
            f"| {row['name']} | {row['value']:.6g} | "
            f"{row['abs_residual']:.6g} | {row['relative_residual']:.6g} |"
        )
    best = payload["best_candidate"]
    lines.extend(
        [
            "",
            "## Best",
            "",
            f"- name: {best['name']}",
            f"- value: {best['value']:.6g}",
            f"- abs residual: {best['abs_residual']:.6g}",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )
    return "\n".join(lines)


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

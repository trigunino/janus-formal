from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.data import ensure_default_data, load_desi_bao

try:
    from scripts.build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_hubble_budget_stress_test.md")
JSON_PATH = Path("outputs/reports/p0_eft_hubble_budget_stress_test.json")


def shape_for_constants(constants: dict, radion: list[dict]) -> np.ndarray:
    dataset = load_desi_bao()
    values = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        row = split_distance_row(float(z), constants, radion, z_sigma=float(constants["z_sigma"]))
        if quantity == "DM_over_rs":
            values.append(row["D_M_unit"])
        elif quantity == "DH_over_rs":
            values.append(row["D_H_unit"])
        elif quantity == "DV_over_rs":
            values.append(row["D_V_unit"])
        else:
            raise ValueError(f"unsupported DESI BAO quantity: {quantity}")
    return np.asarray(values, dtype=float)


def score_variant(name: str, constants: dict, radion: list[dict], changes: dict) -> dict:
    varied = {**constants, **changes}
    try:
        score = score_shape(shape_for_constants(varied, radion))
    except ValueError as exc:
        return {
            "name": name,
            "changes": changes,
            "valid": False,
            "reason": str(exc),
            "chi2": float("inf"),
            "reduced_chi2": float("inf"),
            "scale": float("nan"),
            "DH_diag_chi2": float("inf"),
            "DH_max_abs_pull": float("inf"),
            "DM_diag_chi2": float("inf"),
            "DV_diag_chi2": float("inf"),
        }
    dh = score["by_quantity"]["DH_over_rs"]
    dm = score["by_quantity"]["DM_over_rs"]
    dv = score["by_quantity"]["DV_over_rs"]
    return {
        "name": name,
        "changes": changes,
        "valid": True,
        "reason": "ok",
        "chi2": score["chi2"],
        "reduced_chi2": score["reduced_chi2"],
        "scale": score["scale"],
        "DH_diag_chi2": dh["diag_chi2"],
        "DH_max_abs_pull": dh["max_abs_diag_pull"],
        "DM_diag_chi2": dm["diag_chi2"],
        "DV_diag_chi2": dv["diag_chi2"],
    }


def run_stress_tests() -> dict:
    ensure_default_data()
    constants, radion = master_branch_background(z_max=2.5)
    rows = [
        score_variant("baseline", constants, radion, {}),
        score_variant("spin_zero", constants, radion, {"spin_coeff": 0.0}),
        score_variant("spin_half", constants, radion, {"spin_coeff": 1.0}),
        score_variant("spin_negative", constants, radion, {"spin_coeff": -1.0}),
        score_variant("torsion_today_constant_proxy", constants, radion, {"Omega_T_constant_override": constants["Omega_T0"]}),
    ]
    for omega_m0 in [0.05, 0.1, 0.2, 0.25, 0.3, 0.315, 0.34821190430356097]:
        rows.append(score_variant(f"omega_m0_{omega_m0:g}", constants, radion, {"Omega_m0": omega_m0}))
    valid_rows = [row for row in rows if row["valid"]]
    best_chi2 = min(valid_rows, key=lambda row: row["chi2"])
    best_dh = min(valid_rows, key=lambda row: row["DH_diag_chi2"])
    return {
        "description": "Stress test of the Janus-Holst H(z) budget against DESI DR2 BAO.",
        "status": "hubble-budget-stress-test-computed",
        "baseline_branch": {
            "Omega_m0": constants["Omega_m0"],
            "Omega_T0": constants["Omega_T0"],
            "Omega_dS_residual": constants["Omega_dS_residual"],
            "spin_coeff": constants["spin_coeff"],
        },
        "rows": rows,
        "valid_count": len(valid_rows),
        "best_total_chi2": best_chi2,
        "best_radial_DH": best_dh,
        "diagnosis": (
            "If spin_zero or low Omega_m0 sharply improves DH, the a^-6 spin term or matter budget "
            "is the dominant radial-distance failure. If none improves, the distance/ruler map itself is missing."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Hubble Budget Stress Test",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Baseline Branch",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["baseline_branch"].items())
    lines.extend(
        [
            "",
            "## Variants",
            "",
            "| variant | chi2 | chi2/dof | DH chi2 | DH max pull | DM chi2 | DV chi2 | scale |",
            "|---|---:|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["rows"]:
        lines.append(
            f"| {row['name']} | {row['chi2']:.6g} | {row['reduced_chi2']:.6g} | "
            f"{row['DH_diag_chi2']:.6g} | {row['DH_max_abs_pull']:.6g} | "
            f"{row['DM_diag_chi2']:.6g} | {row['DV_diag_chi2']:.6g} | {row['scale']:.6g} |"
        )
    lines.extend(
        [
            "",
            "## Best",
            "",
            f"- best total chi2: {payload['best_total_chi2']['name']} ({payload['best_total_chi2']['chi2']:.6g})",
            f"- best radial DH: {payload['best_radial_DH']['name']} ({payload['best_radial_DH']['DH_diag_chi2']:.6g})",
            "",
            "## Diagnosis",
            "",
            payload["diagnosis"],
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = run_stress_tests()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

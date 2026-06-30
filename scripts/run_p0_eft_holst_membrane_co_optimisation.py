from __future__ import annotations

from pathlib import Path
import csv
import json

try:
    from scripts.build_p0_eft_cosmological_chi2_calculator import (
        DATA_PATH,
        best_amplitude,
        build_residuals,
        chi2_for_amplitude,
        read_csv,
    )
    from scripts.build_p0_eft_growth_no_fit_numerical_export import branch_constants, integrate_radion
    from scripts.run_p0_eft_holst_immirzi_growth_solver import integrate_growth_holst
    from scripts.run_p0_eft_spinor_torsion_scan import solve_omega_m0_with_spin
except ModuleNotFoundError:
    from build_p0_eft_cosmological_chi2_calculator import (
        DATA_PATH,
        best_amplitude,
        build_residuals,
        chi2_for_amplitude,
        read_csv,
    )
    from build_p0_eft_growth_no_fit_numerical_export import branch_constants, integrate_radion
    from run_p0_eft_holst_immirzi_growth_solver import integrate_growth_holst
    from run_p0_eft_spinor_torsion_scan import solve_omega_m0_with_spin


REPORT_PATH = Path("outputs/reports/p0_eft_holst_membrane_co_optimisation.md")
JSON_PATH = Path("outputs/reports/p0_eft_holst_membrane_co_optimisation.json")
CSV_PATH = Path("outputs/reports/p0_eft_holst_membrane_co_optimisation.csv")


def branch_curve(eta_holst: float, z_sigma: float) -> tuple[dict, list[dict]]:
    mpl2 = 64.0
    eps = -1.0
    h2 = 0.5
    omega_ds = 0.4
    spin_coeff = 2.0
    a_sigma = 1.0 / (1.0 + z_sigma)
    rho_ds = omega_ds * 3.0 * mpl2 * h2
    constants = branch_constants(mpl2=mpl2, eps=eps, h2=h2, rho_ds=rho_ds)
    radion = integrate_radion(constants, a_sigma=a_sigma)
    omega_t0 = radion[-1]["Omega_T"]
    omega_m0 = solve_omega_m0_with_spin(omega_ds, omega_t0, spin_coeff)
    if omega_m0 is None:
        raise ValueError("no positive matter root")
    growth = integrate_growth_holst(constants, radion, omega_m0=omega_m0, eta_holst=eta_holst)
    curve = [{**row, "z": 1.0 / row["a"] - 1.0} for row in growth if 0.0 <= 1.0 / row["a"] - 1.0 <= 2.0]
    return {
        **constants,
        "Omega_m0": omega_m0,
        "Omega_T0": omega_t0,
        "spin_coeff": spin_coeff,
        "eta_holst": eta_holst,
        "z_sigma": z_sigma,
        "a_sigma": a_sigma,
    }, curve


def score_node(data: list[dict], eta_holst: float, z_sigma: float) -> dict:
    try:
        constants, curve = branch_curve(eta_holst, z_sigma)
        if constants["Omega_m0"] <= 0.2:
            return {"eta_holst": eta_holst, "z_sigma": z_sigma, "physical": False, "reason": "Omega_m0 <= 0.2"}
        amp_best = best_amplitude(data, curve)
        chi2_unit = chi2_for_amplitude(data, curve, 1.0)
        chi2_best = chi2_for_amplitude(data, curve, amp_best)
        residuals = build_residuals(data, curve, amp_best)
        qso_pull = next(row["pull"] for row in residuals if row["dataset"] == "eBOSS_DR16_QSO")
        max_abs_pull = max(abs(row["pull"]) for row in residuals)
        return {
            "eta_holst": eta_holst,
            "z_sigma": z_sigma,
            "a_sigma": constants["a_sigma"],
            "Omega_m0": constants["Omega_m0"],
            "Omega_T0": constants["Omega_T0"],
            "physical": True,
            "chi2_unit": chi2_unit,
            "amplitude_best": amp_best,
            "chi2_best": chi2_best,
            "reduced_chi2_best": chi2_best / (len(data) - 1),
            "qso_pull_best": qso_pull,
            "max_abs_pull_best": max_abs_pull,
            "reason": "ok",
        }
    except Exception as exc:
        return {"eta_holst": eta_holst, "z_sigma": z_sigma, "physical": False, "reason": str(exc)}


def run_scan() -> dict:
    data = read_csv(DATA_PATH)
    rows = []
    etas = [round(-2.0 + 0.1 * i, 3) for i in range(21)]
    zsigmas = [round(0.3 + 0.05 * i, 3) for i in range(13)]
    for eta in etas:
        for zsigma in zsigmas:
            rows.append(score_node(data, eta, zsigma))
    physical = [row for row in rows if row.get("physical")]
    by_unit = sorted(physical, key=lambda row: row["chi2_unit"])
    accepted = [row for row in physical if row["chi2_unit"] < 15.0]
    return {
        "description": "Fine co-optimisation of Holst eta_H and membrane redshift z_sigma.",
        "status": "holst-membrane-co-optimisation-computed",
        "rows": rows,
        "physical_count": len(physical),
        "best_unit_amplitude": by_unit[0] if by_unit else None,
        "accepted_count": len(accepted),
        "accepted_best": min(accepted, key=lambda row: row["chi2_unit"]) if accepted else None,
        "criteria": "Omega_m0 > 0.2, chi2_unit < 15",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Holst Membrane Co-Optimisation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physical count: {payload['physical_count']}",
        f"Accepted count: {payload['accepted_count']}",
        f"Criteria: {payload['criteria']}",
        "",
        "## Best Unit Amplitude",
    ]
    if payload["best_unit_amplitude"]:
        lines.extend(f"- {key}: {value}" for key, value in payload["best_unit_amplitude"].items())
    lines.extend(["", "## Accepted Best"])
    if payload["accepted_best"]:
        lines.extend(f"- {key}: {value}" for key, value in payload["accepted_best"].items())
    else:
        lines.append("- none")
    lines.append("")
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, csv_path: Path = CSV_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = run_scan()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        fieldnames = sorted({key for row in payload["rows"] for key in row.keys()})
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(payload["rows"])
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()

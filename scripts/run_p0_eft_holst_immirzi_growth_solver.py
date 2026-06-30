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
    from scripts.build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        integrate_growth,
        integrate_radion,
        rk4_step,
    )
    from scripts.run_p0_eft_spinor_torsion_scan import solve_omega_m0_with_spin
except ModuleNotFoundError:
    from build_p0_eft_cosmological_chi2_calculator import (
        DATA_PATH,
        best_amplitude,
        build_residuals,
        chi2_for_amplitude,
        read_csv,
    )
    from build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        integrate_growth,
        integrate_radion,
        rk4_step,
    )
    from run_p0_eft_spinor_torsion_scan import solve_omega_m0_with_spin


REPORT_PATH = Path("outputs/reports/p0_eft_holst_immirzi_growth_solver.md")
JSON_PATH = Path("outputs/reports/p0_eft_holst_immirzi_growth_solver.json")
CSV_PATH = Path("outputs/reports/p0_eft_holst_immirzi_growth_solver.csv")


def integrate_growth_holst(
    constants: dict,
    radion_rows: list[dict],
    *,
    omega_m0: float,
    eta_holst: float,
    k: float = 1.0,
) -> list[dict]:
    h2 = constants["H2"]
    base_coeff = 161.0 / 36.0
    delta = 1.0e-3
    ddelta = delta
    rows: list[dict] = []
    previous_x = radion_rows[0]["x"]

    def omega_m(a: float) -> float:
        return omega_m0 * a ** -3 / (omega_m0 * a ** -3 + (1 - omega_m0))

    for row in radion_rows:
        x = row["x"]
        dx = x - previous_x
        previous_x = x
        c_eff = base_coeff * (1.0 - eta_holst * row["chi_x"])
        mu = 1.0 + c_eff * row["Omega_T"] * k * k / (k * k + 1.5 * h2)
        if dx:
            def rhs(xx: float, s: tuple[float, float]) -> tuple[float, float]:
                aa = 2.718281828459045 ** xx
                return s[1], -2.0 * s[1] + 1.5 * omega_m(aa) * mu * s[0]

            delta, ddelta = rk4_step((delta, ddelta), x - dx, dx, rhs)
        f = ddelta / delta if delta else 0.0
        rows.append({**row, "c_eff": c_eff, "mu": mu, "delta": delta, "f": f})
    today_delta = rows[-1]["delta"]
    for row in rows:
        row["fsigma8_shape"] = row["f"] * row["delta"] / today_delta
    return rows


def branch_curve(eta_holst: float) -> tuple[dict, list[dict]]:
    mpl2 = 64.0
    eps = -1.0
    h2 = 0.5
    omega_ds = 0.4
    spin_coeff = 2.0
    rho_ds = omega_ds * 3.0 * mpl2 * h2
    constants = branch_constants(mpl2=mpl2, eps=eps, h2=h2, rho_ds=rho_ds)
    radion = integrate_radion(constants)
    omega_t0 = radion[-1]["Omega_T"]
    omega_m0 = solve_omega_m0_with_spin(omega_ds, omega_t0, spin_coeff)
    if omega_m0 is None:
        raise ValueError("no positive matter root")
    growth = integrate_growth_holst(constants, radion, omega_m0=omega_m0, eta_holst=eta_holst)
    curve = [{**row, "z": 1.0 / row["a"] - 1.0} for row in growth if 0.0 <= 1.0 / row["a"] - 1.0 <= 2.0]
    return {**constants, "Omega_m0": omega_m0, "Omega_T0": omega_t0, "spin_coeff": spin_coeff, "eta_holst": eta_holst}, curve


def score_eta(data: list[dict], eta_holst: float) -> dict:
    constants, curve = branch_curve(eta_holst)
    amp_best = best_amplitude(data, curve)
    chi2_unit = chi2_for_amplitude(data, curve, 1.0)
    chi2_best = chi2_for_amplitude(data, curve, amp_best)
    residuals = build_residuals(data, curve, amp_best)
    qso_pull = next(row["pull"] for row in residuals if row["dataset"] == "eBOSS_DR16_QSO")
    return {
        "eta_holst": eta_holst,
        "Omega_m0": constants["Omega_m0"],
        "Omega_T0": constants["Omega_T0"],
        "chi2_unit": chi2_unit,
        "amplitude_best": amp_best,
        "chi2_best": chi2_best,
        "reduced_chi2_best": chi2_best / (len(data) - 1),
        "qso_pull_best": qso_pull,
    }


def run_scan() -> dict:
    data = read_csv(DATA_PATH)
    etas = [round(-8.0 + 0.25 * i, 3) for i in range(65)]
    rows = [score_eta(data, eta) for eta in etas]
    best_unit = min(rows, key=lambda row: row["chi2_unit"])
    accepted = [row for row in rows if row["chi2_unit"] < 15.0]
    return {
        "description": "RUN4 Holst/Immirzi dynamic coefficient scan.",
        "status": "holst-immirzi-scan-computed",
        "ansatz": "C_eff=(161/36)*(1-eta_H*chi_x)",
        "rows": rows,
        "best_unit_amplitude": best_unit,
        "accepted_count": len(accepted),
        "accepted_best": min(accepted, key=lambda row: row["chi2_unit"]) if accepted else None,
        "criteria": "chi2_unit < 15",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Holst Immirzi Growth Solver",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Ansatz: {payload['ansatz']}",
        f"Accepted count: {payload['accepted_count']}",
        f"Criteria: {payload['criteria']}",
        "",
        "## Best Unit Amplitude",
    ]
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
        writer = csv.DictWriter(handle, fieldnames=list(payload["rows"][0].keys()))
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

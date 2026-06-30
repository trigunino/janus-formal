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
    )
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
    )


REPORT_PATH = Path("outputs/reports/p0_eft_anisotropic_pi_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_anisotropic_pi_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_anisotropic_pi_scan.csv")


def derived_omega_m0_pi(constants: dict, radion_rows: list[dict], pi_friedmann: float) -> float:
    omega_t0 = radion_rows[-1]["Omega_T"]
    omega_ds = constants["rho_dS_residual"] / (3.0 * constants["Mpl2"] * constants["H2"])
    return 1.0 - omega_ds - (1.0 - pi_friedmann) * omega_t0


def rescale_curve_mu(curve: list[dict], pi_mu: float) -> list[dict]:
    rows = []
    for row in curve:
        updated = dict(row)
        updated["mu"] = 1.0 + (1.0 + pi_mu) * (row["mu"] - 1.0)
        rows.append(updated)
    return rows


def branch_curve(mpl2: float, eps: float, omega_ds: float, pi_friedmann: float, pi_mu: float) -> tuple[dict, list[dict]]:
    h2 = 0.5
    rho_ds = omega_ds * 3.0 * mpl2 * h2
    constants = branch_constants(mpl2=mpl2, eps=eps, h2=h2, rho_ds=rho_ds)
    radion = integrate_radion(constants)
    omega_m0 = derived_omega_m0_pi(constants, radion, pi_friedmann)
    growth = integrate_growth(constants, radion, omega_m0=omega_m0)
    growth = rescale_curve_mu(growth, pi_mu)
    curve = [{**row, "z": 1.0 / row["a"] - 1.0} for row in growth if 0.0 <= 1.0 / row["a"] - 1.0 <= 2.0]
    return {**constants, "Omega_m0": omega_m0, "Omega_T0": radion[-1]["Omega_T"]}, curve


def score_branch(data: list[dict], mpl2: float, eps: float, omega_ds: float, pi_friedmann: float, pi_mu: float) -> dict:
    try:
        constants, curve = branch_curve(mpl2, eps, omega_ds, pi_friedmann, pi_mu)
        if constants["Omega_m0"] <= 0.2:
            return {
                "eps": eps,
                "Mpl2": mpl2,
                "Omega_dS_residual": omega_ds,
                "pi_friedmann": pi_friedmann,
                "pi_mu": pi_mu,
                "physical": False,
                "reason": "Omega_m0 <= 0.2",
            }
        amp_best = best_amplitude(data, curve)
        chi2_unit = chi2_for_amplitude(data, curve, 1.0)
        chi2_best = chi2_for_amplitude(data, curve, amp_best)
        residuals = build_residuals(data, curve, amp_best)
        qso_pull = next(row["pull"] for row in residuals if row["dataset"] == "eBOSS_DR16_QSO")
        return {
            "eps": eps,
            "Mpl2": mpl2,
            "Omega_dS_residual": omega_ds,
            "pi_friedmann": pi_friedmann,
            "pi_mu": pi_mu,
            "Omega_m0": constants["Omega_m0"],
            "Omega_T0": constants["Omega_T0"],
            "physical": True,
            "chi2_unit": chi2_unit,
            "amplitude_best": amp_best,
            "chi2_best": chi2_best,
            "reduced_chi2_best": chi2_best / (len(data) - 1),
            "qso_pull_best": qso_pull,
            "reason": "ok",
        }
    except Exception as exc:
        return {
            "eps": eps,
            "Mpl2": mpl2,
            "Omega_dS_residual": omega_ds,
            "pi_friedmann": pi_friedmann,
            "pi_mu": pi_mu,
            "physical": False,
            "reason": str(exc),
        }


def run_scan() -> dict:
    data = read_csv(DATA_PATH)
    rows = []
    for eps in (-1.0, 1.0):
        for mpl2 in (4.0, 8.0, 16.0, 32.0, 64.0):
            for omega_ds in (0.02, 0.05, 0.1, 0.2, 0.4, 0.7):
                for pi_friedmann in (0.0, 0.25, 0.5, 0.75, 1.0):
                    for pi_mu in (-0.75, -0.5, -0.25, 0.0, 0.25):
                        rows.append(score_branch(data, mpl2, eps, omega_ds, pi_friedmann, pi_mu))
    physical = [row for row in rows if row.get("physical")]
    by_unit = sorted(physical, key=lambda row: row["chi2_unit"])
    pass_unit = [row for row in physical if row["chi2_unit"] < 15.0]
    return {
        "description": "Controlled anisotropic Pi scan for Friedmann and growth response.",
        "status": "anisotropic-pi-scan-computed",
        "rows": rows,
        "physical_count": len(physical),
        "best_unit_amplitude": by_unit[0] if by_unit else None,
        "pass_unit_count": len(pass_unit),
        "pass_unit_best": sorted(pass_unit, key=lambda row: row["chi2_unit"])[0] if pass_unit else None,
        "criteria": "Omega_m0 > 0.2, chi2_unit < 15",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Anisotropic Pi Scan",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physical count: {payload['physical_count']}",
        f"Pass unit count: {payload['pass_unit_count']}",
        f"Criteria: {payload['criteria']}",
        "",
        "## Best Unit Amplitude",
    ]
    best = payload["best_unit_amplitude"]
    if best:
        lines.extend(f"- {key}: {value}" for key, value in best.items())
    lines.extend(["", "## Pass Unit Best"])
    pass_best = payload["pass_unit_best"]
    if pass_best:
        lines.extend(f"- {key}: {value}" for key, value in pass_best.items())
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

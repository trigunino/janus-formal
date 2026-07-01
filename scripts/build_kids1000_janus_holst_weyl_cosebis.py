from __future__ import annotations

from pathlib import Path
import csv
import json
import math

import numpy as np
from scipy.interpolate import RegularGridInterpolator

try:
    from scripts.build_kids1000_cosebis_contract import (
        cosebis_fits_bytes,
        find_hdu,
        read_binary_table,
        read_fits_hdus,
    )
    from scripts.build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        integrate_radion,
        rk4_step,
    )
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import (
        cosebis_fits_bytes,
        find_hdu,
        read_binary_table,
        read_fits_hdus,
    )
    from build_p0_eft_growth_no_fit_numerical_export import branch_constants, integrate_radion, rk4_step

from janus_lab.cosebis import cosebis_vector_from_xi
from janus_lab.weak_lensing_spectra import janus_xi_curves_for_kids_bins


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_weyl_cosebis.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_weyl_cosebis.json")
CSV_PATH = Path("outputs/reports/kids1000_janus_holst_weyl_cosebis_vector.csv")


def extract_rows() -> tuple[list[dict], list[dict]]:
    fits = cosebis_fits_bytes()
    hdus = read_fits_hdus(fits)
    en_rows = read_binary_table(fits, find_hdu(hdus, "En"))
    nz_rows = read_binary_table(fits, find_hdu(hdus, "NZ_SOURCE"))
    return [row for row in en_rows if 1 <= int(row["ANGBIN"]) <= 5], nz_rows


def interpolate(rows: list[dict], a: np.ndarray, key: str) -> np.ndarray:
    xs = np.asarray([row["a"] for row in rows], dtype=float)
    ys = np.asarray([row[key] for row in rows], dtype=float)
    return np.interp(np.asarray(a, dtype=float), xs, ys)


def integrate_growth_for_k(constants: dict, radion: list[dict], *, omega_m0: float, eta_holst: float, k: float) -> list[dict]:
    h2 = constants["H2"]
    delta = 1.0e-3
    ddelta = delta
    previous_x = radion[0]["x"]
    rows: list[dict] = []

    def omega_m(a: float) -> float:
        return omega_m0 * a**-3 / (omega_m0 * a**-3 + (1.0 - omega_m0))

    for row in radion:
        x = row["x"]
        dx = x - previous_x
        previous_x = x
        c_eff = (161.0 / 36.0) * (1.0 - eta_holst * row["chi_x"])
        mu = 1.0 + c_eff * row["Omega_T"] * k * k / (k * k + 1.5 * h2)
        if dx:
            def rhs(xx: float, state: tuple[float, float]) -> tuple[float, float]:
                aa = math.exp(xx)
                return state[1], -2.0 * state[1] + 1.5 * omega_m(aa) * mu * state[0]

            delta, ddelta = rk4_step((delta, ddelta), x - dx, dx, rhs)
        rows.append({**row, "c_eff": c_eff, "mu": mu, "delta": delta})
    today = rows[-1]["delta"]
    for row in rows:
        row["growth"] = row["delta"] / today
    return rows


def holst_branch(*, eta_holst: float = -1.0) -> tuple[dict, list[dict]]:
    mpl2 = 64.0
    eps = -1.0
    h2 = 0.5
    omega_ds = 0.4
    spin_coeff = 2.0
    rho_ds = omega_ds * 3.0 * mpl2 * h2
    constants = branch_constants(mpl2=mpl2, eps=eps, h2=h2, rho_ds=rho_ds)
    radion = integrate_radion(constants)
    omega_t0 = radion[-1]["Omega_T"]
    # Positive root of spin_coeff*Omega_m0^2 + Omega_m0 + Omega_T0 + omega_ds - 1 = 0.
    c = omega_t0 + omega_ds - 1.0
    disc = 1.0 - 4.0 * spin_coeff * c
    omega_m0 = (-1.0 + math.sqrt(disc)) / (2.0 * spin_coeff)
    return {**constants, "Omega_m0": omega_m0, "Omega_T0": omega_t0, "eta_holst": eta_holst}, radion


def janus_holst_weyl_power_factory(
    *,
    eta_holst: float = -1.0,
    amplitude: float = 1.0e-9,
    spectral_index: float = 1.0,
    k_cut: float = 8.0,
):
    constants, radion = holst_branch(eta_holst=eta_holst)
    k_grid = np.geomspace(1.0e-4, 1.0e2, 96)
    growth_grid = np.asarray(
        [
            [row["growth"] for row in integrate_growth_for_k(constants, radion, omega_m0=constants["Omega_m0"], eta_holst=eta_holst, k=float(k))]
            for k in k_grid
        ],
        dtype=float,
    )
    a_grid = np.asarray([row["a"] for row in radion], dtype=float)
    growth_interp = RegularGridInterpolator(
        (np.log(k_grid), a_grid),
        growth_grid,
        bounds_error=False,
        fill_value=None,
    )
    omega_t_grid = np.asarray([row["Omega_T"] for row in radion], dtype=float)
    chi_x_grid = np.asarray([row["chi_x"] for row in radion], dtype=float)

    def power(k: np.ndarray, z: np.ndarray) -> np.ndarray:
        kk = np.asarray(k, dtype=float)
        aa = 1.0 / (1.0 + np.asarray(z, dtype=float))
        logk = np.log(np.clip(kk, k_grid[0], k_grid[-1]))
        growth = growth_interp(np.column_stack([logk.ravel(), aa.ravel()])).reshape(kk.shape)
        omega_t = np.interp(aa, a_grid, omega_t_grid)
        chi_x = np.interp(aa, a_grid, chi_x_grid)
        c_eff = (161.0 / 36.0) * (1.0 - eta_holst * chi_x)
        mu = 1.0 + c_eff * omega_t * kk * kk / (kk * kk + 1.5 * constants["H2"])
        sigma = mu  # eta_slip=1 branch from the current Weyl source target.
        omega_m = constants["Omega_m0"] * aa**-3 / (constants["Omega_m0"] * aa**-3 + (1.0 - constants["Omega_m0"]))
        primordial = (np.maximum(kk, 1.0e-8) / 0.2) ** spectral_index * np.exp(-(kk / k_cut) ** 2)
        weyl_transfer = 0.75 * omega_m * sigma * growth / np.maximum(kk * kk, 1.0e-8)
        return amplitude * weyl_transfer * weyl_transfer * primordial

    return constants, power


def build_payload() -> dict:
    en_rows, nz_rows = extract_rows()
    theta_arcmin = np.geomspace(0.5, 300.0, 256)
    constants, power = janus_holst_weyl_power_factory()
    xi_plus, xi_minus = janus_xi_curves_for_kids_bins(nz_rows, theta_arcmin, weyl_power=power)
    vector = cosebis_vector_from_xi(theta_arcmin, xi_plus, xi_minus, en_rows, n_max=5)
    rows = [
        {
            "bin1": int(row["BIN1"]),
            "bin2": int(row["BIN2"]),
            "angbin": int(row["ANGBIN"]),
            "janus_holst_cosebis_en": float(value),
        }
        for row, value in zip(en_rows, vector)
    ]
    return {
        "description": "KiDS-1000 COSEBIs vector using a Janus-Holst Weyl power shape.",
        "status": "janus-holst-weyl-cosebis-shape-built",
        "dimension": len(rows),
        "tomographic_pair_count": 15,
        "same_order_as_kids_scale_cut_en": True,
        "weyl_power_provenance": "janus_holst_growth_shape_with_declared_primordial_amplitude",
        "branch": {key: constants[key] for key in ("Omega_m0", "Omega_T0", "eta_holst", "H2")},
        "prediction_ready": False,
        "chi2_ready": False,
        "rows": rows,
        "boundary": (
            "This replaces the toy Weyl scaffold with the existing Janus-Holst mu/growth "
            "shape. The absolute primordial amplitude, nonlinear corrections and value-slip "
            "Green kernel are still declared/open, so no KiDS chi-square claim is allowed."
        ),
    }


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(payload["rows"][0].keys()))
        writer.writeheader()
        writer.writerows(payload["rows"])
    lines = [
        "# KiDS-1000 Janus-Holst Weyl COSEBIs",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Weyl provenance: `{payload['weyl_power_provenance']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| bin1 | bin2 | mode | En shape |",
        "|---:|---:|---:|---:|",
    ]
    for row in payload["rows"][:20]:
        lines.append(f"| {row['bin1']} | {row['bin2']} | {row['angbin']} | {row['janus_holst_cosebis_en']:.6g} |")
    lines.extend(["", payload["boundary"], ""])
    report_path.write_text("\n".join(lines), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()

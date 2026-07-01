from __future__ import annotations

from pathlib import Path
import csv
import json
import math

import matplotlib.pyplot as plt

try:
    from scripts.build_p0_eft_growth_master_branch_export import write_reports as write_master_curve
except ModuleNotFoundError:
    from build_p0_eft_growth_master_branch_export import write_reports as write_master_curve


DATA_PATH = Path("data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_points.csv")
COV_PATH = Path("data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_covariance.csv")
CURVE_PATH = Path("outputs/reports/p0_eft_growth_master_branch_z0_2.csv")
REPORT_PATH = Path("outputs/reports/p0_eft_cosmological_chi2_calculator.md")
JSON_PATH = Path("outputs/reports/p0_eft_cosmological_chi2_calculator.json")
CSV_PATH = Path("outputs/reports/p0_eft_cosmological_chi2_residuals.csv")
PNG_PATH = Path("outputs/reports/p0_eft_cosmological_chi2_residuals.png")


def read_csv(path: Path) -> list[dict]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def read_covariance(path: Path = COV_PATH) -> list[list[float]]:
    rows = read_csv(path)
    keys = [key for key in rows[0].keys() if key not in {"dataset", "z"}]
    return [[float(row[key]) for key in keys] for row in rows]


def solve_linear(matrix: list[list[float]], vector: list[float]) -> list[float]:
    n = len(vector)
    aug = [row[:] + [value] for row, value in zip(matrix, vector)]
    for pivot in range(n):
        best = max(range(pivot, n), key=lambda row: abs(aug[row][pivot]))
        if abs(aug[best][pivot]) < 1e-15:
            raise ValueError("singular covariance")
        aug[pivot], aug[best] = aug[best], aug[pivot]
        scale = aug[pivot][pivot]
        aug[pivot] = [value / scale for value in aug[pivot]]
        for row in range(n):
            if row == pivot:
                continue
            factor = aug[row][pivot]
            aug[row] = [value - factor * base for value, base in zip(aug[row], aug[pivot])]
    return [row[-1] for row in aug]


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def interp_linear(rows: list[dict], z: float, key: str = "fsigma8_shape") -> float:
    points = sorted((float(row["z"]), float(row[key])) for row in rows)
    if z < points[0][0] or z > points[-1][0]:
        raise ValueError(f"z={z} outside curve range")
    for (z0, y0), (z1, y1) in zip(points, points[1:]):
        if z0 <= z <= z1:
            if z1 == z0:
                return y0
            t = (z - z0) / (z1 - z0)
            return y0 + t * (y1 - y0)
    return points[-1][1]


def chi2_for_amplitude(data: list[dict], curve: list[dict], amp: float) -> float:
    total = 0.0
    for row in data:
        model_shape = interp_linear(curve, float(row["z"]))
        residual = amp * model_shape - float(row["fsigma8"])
        sigma = float(row["sigma"])
        total += (residual / sigma) ** 2
    return total


def chi2_for_amplitude_full_cov(
    data: list[dict], curve: list[dict], amp: float, covariance: list[list[float]]
) -> float:
    residual = [amp * interp_linear(curve, float(row["z"])) - float(row["fsigma8"]) for row in data]
    return dot(residual, solve_linear(covariance, residual))


def best_amplitude(data: list[dict], curve: list[dict]) -> float:
    numerator = 0.0
    denominator = 0.0
    for row in data:
        shape = interp_linear(curve, float(row["z"]))
        sigma2 = float(row["sigma"]) ** 2
        numerator += shape * float(row["fsigma8"]) / sigma2
        denominator += shape * shape / sigma2
    return numerator / denominator


def best_amplitude_full_cov(data: list[dict], curve: list[dict], covariance: list[list[float]]) -> float:
    shape = [interp_linear(curve, float(row["z"])) for row in data]
    observed = [float(row["fsigma8"]) for row in data]
    inv_shape = solve_linear(covariance, shape)
    inv_observed = solve_linear(covariance, observed)
    return dot(shape, inv_observed) / dot(shape, inv_shape)


def build_residuals(data: list[dict], curve: list[dict], amp: float) -> list[dict]:
    residuals = []
    for row in data:
        z = float(row["z"])
        shape = interp_linear(curve, z)
        model = amp * shape
        data_value = float(row["fsigma8"])
        sigma = float(row["sigma"])
        residuals.append(
            {
                "dataset": row["dataset"],
                "z": z,
                "data": data_value,
                "sigma": sigma,
                "janus_shape": shape,
                "amplitude": amp,
                "janus_model": model,
                "residual": model - data_value,
                "pull": (model - data_value) / sigma,
            }
        )
    return residuals


def render_plot(residuals: list[dict], curve: list[dict], amp: float, png_path: Path = PNG_PATH) -> None:
    png_path.parent.mkdir(parents=True, exist_ok=True)
    z_curve = [float(row["z"]) for row in curve]
    y_curve = [amp * float(row["fsigma8_shape"]) for row in curve]
    z_data = [row["z"] for row in residuals]
    y_data = [row["data"] for row in residuals]
    y_err = [row["sigma"] for row in residuals]
    fig, ax = plt.subplots(figsize=(7, 4))
    ax.plot(z_curve, y_curve, color="#1f77b4", label="Janus scaled")
    ax.errorbar(z_data, y_data, yerr=y_err, fmt="o", color="#111111", label="SDSS/eBOSS DR16")
    ax.set_xlabel("z")
    ax.set_ylabel("f sigma8")
    ax.invert_xaxis()
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(png_path, dpi=160)
    plt.close(fig)


def build_payload() -> dict:
    data = read_csv(DATA_PATH)
    covariance = read_covariance(COV_PATH)
    if not CURVE_PATH.exists():
        write_master_curve()
    curve = read_csv(CURVE_PATH)
    amp_best = best_amplitude(data, curve)
    chi2_best = chi2_for_amplitude(data, curve, amp_best)
    chi2_unit = chi2_for_amplitude(data, curve, 1.0)
    amp_best_full = best_amplitude_full_cov(data, curve, covariance)
    chi2_best_full = chi2_for_amplitude_full_cov(data, curve, amp_best_full, covariance)
    chi2_unit_full = chi2_for_amplitude_full_cov(data, curve, 1.0, covariance)
    residuals = build_residuals(data, curve, amp_best)
    dof_best = len(data) - 1
    render_plot(residuals, curve, amp_best)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(residuals[0].keys()))
        writer.writeheader()
        writer.writerows(residuals)
    return {
        "description": "SDSS/eBOSS-only chi2 check for the Janus master branch f_sigma8 shape.",
        "status": "sdss-chi2-computed",
        "data_points": len(data),
        "amplitude_best": amp_best,
        "chi2_unit_amplitude": chi2_unit,
        "chi2_best_amplitude": chi2_best,
        "full_covariance_used": True,
        "chi2_unit_amplitude_full_covariance": chi2_unit_full,
        "amplitude_best_full_covariance": amp_best_full,
        "chi2_best_amplitude_full_covariance": chi2_best_full,
        "dof_best_amplitude": dof_best,
        "reduced_chi2_best": chi2_best / dof_best if dof_best > 0 else None,
        "reduced_chi2_best_full_covariance": chi2_best_full / dof_best if dof_best > 0 else None,
        "outputs": {"residuals_csv": str(CSV_PATH), "plot_png": str(PNG_PATH)},
        "residuals": residuals,
        "notes": [
            "Uses the reduced SDSS/eBOSS DR16 f_sigma8 covariance, including the BOSS DR12 cross-redshift term.",
            "Best amplitude is a normalization of the exported shape, not a refit of Janus branch dynamics.",
            "DESI/Planck priors remain open.",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Cosmological Chi2 Calculator",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Data points: {payload['data_points']}",
        f"Best amplitude: {payload['amplitude_best']:.6g}",
        f"Chi2 unit amplitude: {payload['chi2_unit_amplitude']:.6g}",
        f"Chi2 best amplitude: {payload['chi2_best_amplitude']:.6g}",
        f"Reduced chi2 best: {payload['reduced_chi2_best']:.6g}",
        f"Chi2 unit amplitude full covariance: {payload['chi2_unit_amplitude_full_covariance']:.6g}",
        f"Best amplitude full covariance: {payload['amplitude_best_full_covariance']:.6g}",
        f"Chi2 best amplitude full covariance: {payload['chi2_best_amplitude_full_covariance']:.6g}",
        f"Reduced chi2 best full covariance: {payload['reduced_chi2_best_full_covariance']:.6g}",
        "",
        "## Residuals",
        "",
        "| dataset | z | data | model | sigma | pull |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for row in payload["residuals"]:
        lines.append(
            f"| {row['dataset']} | {row['z']:.3f} | {row['data']:.6g} | "
            f"{row['janus_model']:.6g} | {row['sigma']:.6g} | {row['pull']:.3f} |"
        )
    lines.extend(["", "## Notes"])
    lines.extend(f"- {note}" for note in payload["notes"])
    lines.append("")
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
    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {PNG_PATH}")


if __name__ == "__main__":
    main()

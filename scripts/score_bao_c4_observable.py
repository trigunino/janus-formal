from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion
from janus_lab.bao_maps import gauge_weighted_open_marker
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.models import janus_q0_from_u0
from janus_lab.statistics import FitResult, chi_square


REPORT_PATH = Path("outputs/reports/janus_bao_c4_observable_score.md")
CSV_PATH = Path("outputs/reports/janus_bao_c4_observable_predictions.csv")


@dataclass(frozen=True)
class C4Fit:
    q0: float
    scale: float
    transverse_power: float
    radial_power: float
    chi2: float
    prediction: np.ndarray

    @property
    def fit(self) -> FitResult:
        return FitResult(
            name=f"C4 gauge observable, q0={self.q0:.4f}",
            chi2=self.chi2,
            n_data=len(self.prediction),
            n_params=4,
            params={
                "q0": self.q0,
                "scale": self.scale,
                "transverse_power": self.transverse_power,
                "radial_power": self.radial_power,
            },
        )


def fit_linear_scale(shape: np.ndarray, observed: np.ndarray, covariance: np.ndarray) -> tuple[float, np.ndarray, float]:
    inv_cov = np.linalg.inv(covariance)
    scale = float(shape @ inv_cov @ observed / (shape @ inv_cov @ shape))
    prediction = scale * shape
    return scale, prediction, chi_square(observed - prediction, covariance=covariance)


def c4_shape(
    z: np.ndarray,
    quantities: np.ndarray,
    marker: np.ndarray,
    e_value: np.ndarray,
    q0: float,
    radial_power: float,
) -> np.ndarray:
    dm_shape = marker / np.sqrt(1.0 - 2.0 * q0)
    dh_shape = (1.0 / (1.0 + z)) ** radial_power / e_value
    dv_shape = np.cbrt(z * dm_shape**2 * dh_shape)

    values = np.empty_like(z)
    values[quantities == "DM_over_rs"] = dm_shape[quantities == "DM_over_rs"]
    values[quantities == "DH_over_rs"] = dh_shape[quantities == "DH_over_rs"]
    values[quantities == "DV_over_rs"] = dv_shape[quantities == "DV_over_rs"]
    return values


def fit_c4_for_q0(q0: float) -> C4Fit:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    e_value = np.asarray(model.e(dataset.z), dtype=float)
    q0_value = janus_q0_from_u0(model.u0)
    best: tuple[float, float, float, float, np.ndarray] | None = None
    t_center, r_center = 0.0, 0.0
    t_width, r_width = 2.0, 2.0

    for _ in range(4):
        t_grid = np.linspace(t_center - t_width, t_center + t_width, 41)
        r_grid = np.linspace(r_center - r_width, r_center + r_width, 41)
        for transverse_power in t_grid:
            marker = np.asarray(
                gauge_weighted_open_marker(
                    dataset.z,
                    model,
                    gauge_power=float(transverse_power),
                    samples=384,
                ),
                dtype=float,
            )
            for radial_power in r_grid:
                shape = c4_shape(
                    dataset.z,
                    dataset.quantity,
                    marker,
                    e_value,
                    q0_value,
                    float(radial_power),
                )
                scale, prediction, chi2 = fit_linear_scale(shape, dataset.value, dataset.covariance)
                if best is None or chi2 < best[0]:
                    best = (
                        chi2,
                        scale,
                        float(transverse_power),
                        float(radial_power),
                        prediction,
                    )
        assert best is not None
        _, _, t_center, r_center, _ = best
        t_width /= 5.0
        r_width /= 5.0

    chi2, scale, transverse_power, radial_power, prediction = best
    return C4Fit(
        q0=q0,
        scale=scale,
        transverse_power=transverse_power,
        radial_power=radial_power,
        chi2=chi2,
        prediction=prediction,
    )


def format_fit(fit: FitResult) -> str:
    params = ", ".join(f"{key}={value:.6g}" for key, value in fit.params.items())
    return (
        f"| {fit.name} | {fit.chi2:.3f} | {fit.dof} | {fit.chi2_per_dof:.3f} | "
        f"{fit.aic:.3f} | {fit.bic:.3f} | {params} |"
    )


def main() -> None:
    ensure_default_data()
    dataset = load_desi_bao()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    q0_grid = [-0.001, -0.003, -0.005, -0.01, -0.02, -0.03, -0.05, -0.087]
    fits = [fit_c4_for_q0(q0) for q0 in q0_grid]
    best = sorted(fits, key=lambda item: item.fit.aic)[0]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("z,quantity,observed,predicted,residual\n")
        for z, quantity, observed, predicted in zip(
            dataset.z,
            dataset.quantity,
            dataset.value,
            best.prediction,
        ):
            handle.write(
                f"{z:.8g},{quantity},{observed:.10g},{predicted:.10g},{observed - predicted:.10g}\n"
            )

    lines = [
        "# Janus BAO C4 Observable Score",
        "",
        "C4 changes the observable map itself:",
        "",
        "- transverse path: `dchi -> a(u)^p_T dchi` before the open `sinh` marker;",
        "- radial observable: `D_H -> a(z)^p_R / E(z)`;",
        "- `D_V` remains the compressed geometric combination;",
        "- one global scale is fitted for all quantities.",
        "",
        "This is still phenomenological, but it tests whether changing `D_M/D_H` is more promising than changing only `r_d`.",
        "",
        "## Fits",
        "",
        "| Model | chi2 | dof | chi2/dof | AIC | BIC | params |",
        "|---|---:|---:|---:|---:|---:|---|",
    ]
    for fit in sorted(fits, key=lambda item: item.fit.aic):
        lines.append(format_fit(fit.fit))
    lines.extend(
        [
            "",
            f"Best predictions CSV: `{CSV_PATH}`",
            "",
            "## Reading",
            "",
            "- If C4 beats C2b, changing the observable map is the right direction.",
            "- If C4 still prefers `q0` close to zero, the current Janus expansion branch conflicts with compressed DESI BAO unless another physical ingredient is missing.",
            "- The fitted powers are diagnostic only until derived from the variable-constants regime.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(format_fit(best.fit))


if __name__ == "__main__":
    main()

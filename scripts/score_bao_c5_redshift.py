from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion
from janus_lab.bao_maps import janus_c5_redshift_prediction
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import FitResult, chi_square


REPORT_PATH = Path("outputs/reports/janus_bao_c5_redshift_score.md")
CSV_PATH = Path("outputs/reports/janus_bao_c5_redshift_predictions.csv")


@dataclass(frozen=True)
class C5Fit:
    q0: float
    gamma: float
    scale: float
    compression_z: str
    chi2: float
    prediction: np.ndarray

    @property
    def fit(self) -> FitResult:
        return FitResult(
            name=f"C5 redshift remap, q0={self.q0:.4f}, {self.compression_z}",
            chi2=self.chi2,
            n_data=len(self.prediction),
            n_params=3,
            params={"q0": self.q0, "gamma": self.gamma, "scale": self.scale},
        )


def fit_linear_scale(shape: np.ndarray, observed: np.ndarray, covariance: np.ndarray) -> tuple[float, np.ndarray, float]:
    inv_cov = np.linalg.inv(covariance)
    scale = float(shape @ inv_cov @ observed / (shape @ inv_cov @ shape))
    prediction = scale * shape
    return scale, prediction, chi_square(observed - prediction, covariance=covariance)


def c5_shape(model: JanusExpansion, gamma: float, compression_z: str) -> np.ndarray | None:
    dataset = load_desi_bao()
    values = []
    try:
        for z, quantity in zip(dataset.z, dataset.quantity):
            values.append(
                janus_c5_redshift_prediction(
                    float(z),
                    str(quantity),
                    model,
                    scale=1.0,
                    gamma=gamma,
                    compression_z=compression_z,
                )
            )
    except ValueError:
        return None
    return np.asarray(values, dtype=float)


def fit_c5_for_q0(q0: float, compression_z: str) -> C5Fit:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    best: tuple[float, float, float, np.ndarray] | None = None
    gamma_center = 1.0
    gamma_width = 0.9

    for _ in range(5):
        gamma_grid = np.linspace(
            max(0.05, gamma_center - gamma_width),
            gamma_center + gamma_width,
            121,
        )
        for gamma in gamma_grid:
            shape = c5_shape(model, float(gamma), compression_z)
            if shape is None or not np.all(np.isfinite(shape)):
                continue
            scale, prediction, chi2 = fit_linear_scale(shape, dataset.value, dataset.covariance)
            if best is None or chi2 < best[0]:
                best = (chi2, float(gamma), scale, prediction)
        assert best is not None
        _, gamma_center, _, _ = best
        gamma_width /= 6.0

    chi2, gamma, scale, prediction = best
    return C5Fit(
        q0=q0,
        gamma=gamma,
        scale=scale,
        compression_z=compression_z,
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
    fits: list[C5Fit] = []
    for q0 in q0_grid:
        for compression_z in ["observed", "geometric"]:
            fits.append(fit_c5_for_q0(q0, compression_z))
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
        "# Janus BAO C5 Redshift Score",
        "",
        "C5 tests whether observed DESI redshift and Janus geometric redshift differ:",
        "",
        "`1 + z_geom = (1 + z_obs)^gamma`",
        "",
        "A single global scale is fitted. Two `D_V` compression choices are tested:",
        "",
        "- `observed`: keep DESI's reported redshift in `D_V`;",
        "- `geometric`: use the remapped Janus redshift in `D_V`.",
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
            "- If C5 beats C4, redshift definition is a plausible missing ingredient.",
            "- If C5 still prefers `q0` close to zero, redshift remapping alone does not rescue the SN-preferred Janus branch.",
            "- If `gamma` is far from 1, the implied redshift law must be derived from the variable-constants regime before any physical claim.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(format_fit(best.fit))


if __name__ == "__main__":
    main()

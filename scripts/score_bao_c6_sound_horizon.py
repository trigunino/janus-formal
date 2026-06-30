from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion
from janus_lab.bao_maps import janus_c6_common_ruler_prediction
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import FitResult, chi_square


REPORT_PATH = Path("outputs/reports/janus_bao_c6_sound_horizon_score.md")
CSV_PATH = Path("outputs/reports/janus_bao_c6_sound_horizon_predictions.csv")


@dataclass(frozen=True)
class C6Fit:
    q0: float
    scale: float
    ruler_power: float
    chi2: float
    base_chi2: float
    prediction: np.ndarray

    @property
    def fit(self) -> FitResult:
        return FitResult(
            name=f"C6 common sound horizon, q0={self.q0:.4f}",
            chi2=self.chi2,
            n_data=len(self.prediction),
            n_params=3,
            params={
                "q0": self.q0,
                "scale": self.scale,
                "ruler_power": self.ruler_power,
                "base_chi2": self.base_chi2,
            },
        )


def fit_linear_scale(shape: np.ndarray, observed: np.ndarray, covariance: np.ndarray) -> tuple[float, np.ndarray, float]:
    inv_cov = np.linalg.inv(covariance)
    scale = float(shape @ inv_cov @ observed / (shape @ inv_cov @ shape))
    prediction = scale * shape
    return scale, prediction, chi_square(observed - prediction, covariance=covariance)


def c6_shape(model: JanusExpansion, ruler_power: float) -> np.ndarray:
    dataset = load_desi_bao()
    return np.asarray(
        [
            janus_c6_common_ruler_prediction(
                float(z),
                str(quantity),
                model,
                scale=1.0,
                ruler_power=ruler_power,
            )
            for z, quantity in zip(dataset.z, dataset.quantity)
        ],
        dtype=float,
    )


def fit_c6_for_q0(q0: float) -> C6Fit:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    _, _, base_chi2 = fit_linear_scale(c6_shape(model, 0.0), dataset.value, dataset.covariance)
    best: tuple[float, float, float, np.ndarray] | None = None
    power_center = 0.0
    power_width = 2.0

    for _ in range(5):
        for ruler_power in np.linspace(power_center - power_width, power_center + power_width, 241):
            shape = c6_shape(model, float(ruler_power))
            scale, prediction, chi2 = fit_linear_scale(shape, dataset.value, dataset.covariance)
            if best is None or chi2 < best[0]:
                best = (chi2, float(ruler_power), scale, prediction)
        assert best is not None
        _, power_center, _, _ = best
        power_width /= 6.0

    chi2, ruler_power, scale, prediction = best
    return C6Fit(
        q0=q0,
        scale=scale,
        ruler_power=ruler_power,
        chi2=chi2,
        base_chi2=base_chi2,
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
    fits = [fit_c6_for_q0(q0) for q0 in q0_grid]
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
        "# Janus BAO C6 Sound-Horizon Score",
        "",
        "C6 tests whether the missing BAO ingredient can be represented as one common effective ruler:",
        "",
        "`S(z) = A * (1 + z)^p`",
        "",
        "`p=0` is a constant sound horizon and is exactly the already-fitted global BAO scale.",
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
            "- A constant `r_d` cannot solve the BAO shape tension because it is only the global scale already fitted.",
            "- A common evolving ruler improves over C0/C5 but remains worse than C4.",
            "- At fixed supernova-like `q0=-0.087`, C6 remains poor, so the missing ingredient is not a single common sound-horizon power.",
            "- The next viable tests are quantity-dependent ruler formation, DESI fiducial compression, or uncompressed BAO likelihood.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(format_fit(best.fit))


if __name__ == "__main__":
    main()

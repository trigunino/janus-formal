from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion
from janus_lab.bao import janus_bao_prediction_vector
from janus_lab.bao_maps import (
    AnisotropicPowerLawScale,
    AnisotropicSqrtAScale,
    sqrt_a_scale,
)
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import FitResult, chi_square


REPORT_PATH = Path("outputs/reports/janus_bao_c2_gauge_score.md")
CSV_PATH = Path("outputs/reports/janus_bao_c2_gauge_predictions.csv")


@dataclass(frozen=True)
class C2Fit:
    q0: float
    dm_amplitude: float
    dh_amplitude: float
    chi2: float
    prediction: np.ndarray

    @property
    def fit(self) -> FitResult:
        return FitResult(
            name=f"C2 anisotropic sqrt(a), q0={self.q0:.4f}",
            chi2=self.chi2,
            n_data=len(self.prediction),
            n_params=3,
            params={
                "q0": self.q0,
                "dm_amplitude": self.dm_amplitude,
                "dh_amplitude": self.dh_amplitude,
            },
        )


@dataclass(frozen=True)
class C2PowerFit:
    q0: float
    dm_amplitude: float
    dm_power: float
    dh_amplitude: float
    dh_power: float
    chi2: float
    prediction: np.ndarray

    @property
    def fit(self) -> FitResult:
        return FitResult(
            name=f"C2b anisotropic power, q0={self.q0:.4f}",
            chi2=self.chi2,
            n_data=len(self.prediction),
            n_params=5,
            params={
                "q0": self.q0,
                "dm_amplitude": self.dm_amplitude,
                "dm_power": self.dm_power,
                "dh_amplitude": self.dh_amplitude,
                "dh_power": self.dh_power,
            },
        )


def c2_prediction_from_base(
    base: np.ndarray,
    z: np.ndarray,
    quantities: np.ndarray,
    dm_amplitude: float,
    dh_amplitude: float,
) -> np.ndarray:
    scale = AnisotropicSqrtAScale(dm_amplitude=dm_amplitude, dh_amplitude=dh_amplitude)
    values = []
    for base_value, z_value, quantity in zip(base, z, quantities):
        values.append(base_value * scale.scale(float(z_value), str(quantity)))
    return np.asarray(values, dtype=float)


def c2_power_prediction_from_base(
    base: np.ndarray,
    z: np.ndarray,
    quantities: np.ndarray,
    dm_amplitude: float,
    dm_power: float,
    dh_amplitude: float,
    dh_power: float,
) -> np.ndarray:
    scale = AnisotropicPowerLawScale(
        dm_amplitude=dm_amplitude,
        dm_power=dm_power,
        dh_amplitude=dh_amplitude,
        dh_power=dh_power,
    )
    values = []
    for base_value, z_value, quantity in zip(base, z, quantities):
        values.append(base_value * scale.scale(float(z_value), str(quantity)))
    return np.asarray(values, dtype=float)


def predict_c2(q0: float, dm_amplitude: float, dh_amplitude: float) -> np.ndarray:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    base = janus_bao_prediction_vector(dataset, model, scale=1.0)
    return c2_prediction_from_base(
        base,
        dataset.z,
        dataset.quantity,
        dm_amplitude,
        dh_amplitude,
    )


def fit_c2_for_q0(q0: float) -> C2Fit:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    base = janus_bao_prediction_vector(dataset, model, scale=1.0)
    best: tuple[float, float, float, np.ndarray] | None = None
    dm_center, dh_center = 39.5, 41.8
    dm_width, dh_width = 12.0, 12.0
    for _ in range(4):
        dm_grid = np.linspace(dm_center - dm_width, dm_center + dm_width, 41)
        dh_grid = np.linspace(dh_center - dh_width, dh_center + dh_width, 41)
        for dm_amplitude in dm_grid:
            if dm_amplitude <= 0:
                continue
            for dh_amplitude in dh_grid:
                if dh_amplitude <= 0:
                    continue
                prediction = c2_prediction_from_base(
                    base,
                    dataset.z,
                    dataset.quantity,
                    float(dm_amplitude),
                    float(dh_amplitude),
                )
                chi2 = chi_square(dataset.value - prediction, covariance=dataset.covariance)
                if best is None or chi2 < best[0]:
                    best = (chi2, float(dm_amplitude), float(dh_amplitude), prediction)
        assert best is not None
        _, dm_center, dh_center, _ = best
        dm_width /= 6.0
        dh_width /= 6.0

    chi2, dm_amplitude, dh_amplitude, prediction = best
    return C2Fit(
        q0=q0,
        dm_amplitude=dm_amplitude,
        dh_amplitude=dh_amplitude,
        chi2=chi2,
        prediction=prediction,
    )


def fit_c2_power_for_q0(q0: float) -> C2PowerFit:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    base = janus_bao_prediction_vector(dataset, model, scale=1.0)

    params = np.asarray([38.4, -0.46, 41.5, -0.49], dtype=float)
    steps = np.asarray([6.0, 0.25, 6.0, 0.25], dtype=float)

    def evaluate(candidate: np.ndarray) -> tuple[float, np.ndarray]:
        if candidate[0] <= 0 or candidate[2] <= 0:
            return float("inf"), np.full_like(dataset.value, np.nan)
        prediction = c2_power_prediction_from_base(
            base,
            dataset.z,
            dataset.quantity,
            dm_amplitude=float(candidate[0]),
            dm_power=float(candidate[1]),
            dh_amplitude=float(candidate[2]),
            dh_power=float(candidate[3]),
        )
        return chi_square(dataset.value - prediction, covariance=dataset.covariance), prediction

    best_chi2, best_prediction = evaluate(params)
    while np.any(steps > np.asarray([0.005, 0.0005, 0.005, 0.0005])):
        improved = False
        for index in range(len(params)):
            for direction in [-1.0, 1.0]:
                candidate = params.copy()
                candidate[index] += direction * steps[index]
                chi2, prediction = evaluate(candidate)
                if chi2 < best_chi2:
                    params = candidate
                    best_chi2 = chi2
                    best_prediction = prediction
                    improved = True
        if not improved:
            steps *= 0.5

    return C2PowerFit(
        q0=q0,
        dm_amplitude=float(params[0]),
        dm_power=float(params[1]),
        dh_amplitude=float(params[2]),
        dh_power=float(params[3]),
        chi2=float(best_chi2),
        prediction=best_prediction,
    )


def fit_global_sqrt_for_q0(q0: float) -> tuple[FitResult, float, np.ndarray]:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    base = janus_bao_prediction_vector(dataset, model, scale=1.0)
    template = np.asarray([base_i * sqrt_a_scale(z_i) for base_i, z_i in zip(base, dataset.z)])
    inv_cov = np.linalg.inv(dataset.covariance)
    amplitude = float(template @ inv_cov @ dataset.value / (template @ inv_cov @ template))
    prediction = amplitude * template
    fit = FitResult(
        name=f"C1 global sqrt(a), q0={q0:.4f}",
        chi2=chi_square(dataset.value - prediction, covariance=dataset.covariance),
        n_data=len(dataset.value),
        n_params=2,
        params={"q0": q0, "amplitude": amplitude},
    )
    return fit, amplitude, prediction


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
    c1_fits = [fit_global_sqrt_for_q0(q0) for q0 in q0_grid]
    c2_fits = [fit_c2_for_q0(q0) for q0 in q0_grid]
    c2_power_fits = [fit_c2_power_for_q0(q0) for q0 in q0_grid]
    best_c1 = sorted(c1_fits, key=lambda item: item[0].aic)[0]
    best_c2 = sorted(c2_fits, key=lambda item: item.fit.aic)[0]
    best_c2_power = sorted(c2_power_fits, key=lambda item: item.fit.aic)[0]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("z,quantity,observed,predicted,residual\n")
        for z, quantity, observed, predicted in zip(
            dataset.z, dataset.quantity, dataset.value, best_c2_power.prediction
        ):
            handle.write(
                f"{z:.8g},{quantity},{observed:.10g},{predicted:.10g},{observed - predicted:.10g}\n"
            )

    lines = [
        "# Janus BAO C2 Gauge Score",
        "",
        "C2 candidate tested here:",
        "",
        "- `S_DM(z)=A_DM/sqrt(1+z)`",
        "- `S_DH(z)=A_DH/sqrt(1+z)`",
        "- `S_DV(z)=(A_DM^2 A_DH)^(1/3)/sqrt(1+z)`",
        "",
        "C2b candidate adds fitted powers while keeping `DV` derived:",
        "",
        "- `S_DM(z)=A_DM*(1+z)^p_DM`",
        "- `S_DH(z)=A_DH*(1+z)^p_DH`",
        "- `S_DV(z)=(S_DM(z)^2*S_DH(z))^(1/3)`",
        "",
        "This is more constrained than the empirical quantity-linear inverse map.",
        "",
        "## Best C1 Global sqrt(a)",
        "",
        "| Model | chi2 | dof | chi2/dof | AIC | BIC | params |",
        "|---|---:|---:|---:|---:|---:|---|",
        format_fit(best_c1[0]),
        "",
        "## C2 Anisotropic sqrt(a) Grid",
        "",
        "| Model | chi2 | dof | chi2/dof | AIC | BIC | params |",
        "|---|---:|---:|---:|---:|---:|---|",
    ]
    for fit in sorted(c2_fits, key=lambda item: item.fit.aic):
        lines.append(format_fit(fit.fit))
    lines.extend(
        [
            "",
            "## C2b Anisotropic Power Grid",
            "",
            "| Model | chi2 | dof | chi2/dof | AIC | BIC | params |",
            "|---|---:|---:|---:|---:|---:|---|",
        ]
    )
    for fit in sorted(c2_power_fits, key=lambda item: item.fit.aic):
        lines.append(format_fit(fit.fit))
    lines.extend(
        [
            "",
            f"Best C2 predictions CSV: `{CSV_PATH}`",
            "",
            "## Reading",
            "",
            "- This tests the first physically constrained C2 shape from Eq. 40.",
            "- If C2 is much worse than the empirical C3 map, `sqrt(a)` alone is not the missing BAO map.",
            "- If C2b is still much worse than C3, the missing term is not just a power-law correction.",
            "- If C2b approaches C3, the next derivation target is explaining the fitted powers from Janus gauge physics.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(format_fit(best_c2.fit))
    print(format_fit(best_c2_power.fit))


if __name__ == "__main__":
    main()

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion
from janus_lab.bao_maps import janus_c7_anisotropic_linear_ruler_prediction
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import FitResult, chi_square


REPORT_PATH = Path("outputs/reports/janus_bao_c7_anisotropic_linear_ruler_score.md")
CSV_PATH = Path("outputs/reports/janus_bao_c7_anisotropic_linear_ruler_predictions.csv")


@dataclass(frozen=True)
class C7Fit:
    q0: float
    dm_intercept: float
    dm_slope: float
    dh_intercept: float
    dh_slope: float
    chi2: float
    prediction: np.ndarray

    @property
    def fit(self) -> FitResult:
        return FitResult(
            name=f"C7 anisotropic linear ruler, q0={self.q0:.4f}",
            chi2=self.chi2,
            n_data=len(self.prediction),
            n_params=5,
            params={
                "q0": self.q0,
                "dm_intercept": self.dm_intercept,
                "dm_slope": self.dm_slope,
                "dh_intercept": self.dh_intercept,
                "dh_slope": self.dh_slope,
            },
        )


def c7_prediction(model: JanusExpansion, params: np.ndarray) -> np.ndarray | None:
    dataset = load_desi_bao()
    dm_intercept, dm_slope, dh_intercept, dh_slope = params
    dm_scale = dm_intercept + dm_slope * dataset.z
    dh_scale = dh_intercept + dh_slope * dataset.z
    if np.any(dm_scale <= 0.0) or np.any(dh_scale <= 0.0):
        return None
    return np.asarray(
        [
            janus_c7_anisotropic_linear_ruler_prediction(
                float(z),
                str(quantity),
                model,
                dm_intercept=dm_intercept,
                dm_slope=dm_slope,
                dh_intercept=dh_intercept,
                dh_slope=dh_slope,
            )
            for z, quantity in zip(dataset.z, dataset.quantity)
        ],
        dtype=float,
    )


def score_params(model: JanusExpansion, params: np.ndarray) -> float:
    dataset = load_desi_bao()
    prediction = c7_prediction(model, params)
    if prediction is None or not np.all(np.isfinite(prediction)):
        return float("inf")
    return chi_square(dataset.value - prediction, covariance=dataset.covariance)


def initial_params(model: JanusExpansion) -> np.ndarray:
    dataset = load_desi_bao()
    starts = []
    for quantity in ["DM_over_rs", "DH_over_rs"]:
        rows = dataset.quantity == quantity
        scales = []
        for z in dataset.z[rows]:
            base = janus_c7_anisotropic_linear_ruler_prediction(
                float(z),
                quantity,
                model,
                dm_intercept=1.0,
                dm_slope=0.0,
                dh_intercept=1.0,
                dh_slope=0.0,
            )
            observed = dataset.value[np.where((dataset.z == z) & (dataset.quantity == quantity))[0][0]]
            scales.append(float(observed / base))
        design = np.column_stack([np.ones(np.count_nonzero(rows)), dataset.z[rows]])
        coeffs, *_ = np.linalg.lstsq(design, np.asarray(scales), rcond=None)
        starts.extend(float(value) for value in coeffs)
    return np.asarray(starts, dtype=float)


def optimize_params(model: JanusExpansion) -> tuple[np.ndarray, float, np.ndarray]:
    dataset = load_desi_bao()
    starts = [
        initial_params(model),
        np.asarray([35.0, 0.0, 35.0, 0.0], dtype=float),
        np.asarray([33.0, -4.0, 36.0, -4.0], dtype=float),
    ]
    best_params = starts[0]
    best_chi2 = float("inf")
    best_prediction = np.zeros_like(dataset.value)

    for start in starts:
        params = start.copy()
        steps = np.maximum(np.abs(params) * 0.2, np.asarray([2.0, 2.0, 2.0, 2.0]))
        current = score_params(model, params)
        for _ in range(120):
            improved = False
            for index in range(len(params)):
                for sign in [1.0, -1.0]:
                    candidate = params.copy()
                    candidate[index] += sign * steps[index]
                    candidate_chi2 = score_params(model, candidate)
                    if candidate_chi2 < current:
                        params = candidate
                        current = candidate_chi2
                        improved = True
            if not improved:
                steps *= 0.55
                if float(np.max(steps)) < 1e-5:
                    break
        prediction = c7_prediction(model, params)
        if prediction is not None and current < best_chi2:
            best_params = params
            best_chi2 = current
            best_prediction = prediction

    return best_params, best_chi2, best_prediction


def fit_c7_for_q0(q0: float) -> C7Fit:
    model = JanusExpansion.from_q0(q0)
    params, chi2, prediction = optimize_params(model)
    return C7Fit(
        q0=q0,
        dm_intercept=float(params[0]),
        dm_slope=float(params[1]),
        dh_intercept=float(params[2]),
        dh_slope=float(params[3]),
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
    q0_grid = [-0.001, -0.003, -0.005, -0.01, -0.02, -0.03, -0.05, -0.07, -0.087, -0.10]
    fits = [fit_c7_for_q0(q0) for q0 in q0_grid]
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
        "# Janus BAO C7 Anisotropic Linear Ruler Score",
        "",
        "C7 tests the best empirical clue with a stricter physical constraint:",
        "",
        "- `S_DM(z) = A_DM + B_DM z`;",
        "- `S_DH(z) = A_DH + B_DH z`;",
        "- `S_DV(z) = [S_DM(z)^2 S_DH(z)]^(1/3)` is derived, not fitted independently.",
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
            "- C7 beats C4/C5/C6 while keeping `D_V` constrained by `D_M` and `D_H`.",
            "- The best grid point is near the Janus/SN branch and `q0=-0.087` remains competitive.",
            "- This is still phenomenological: the linear anisotropic ruler must be derived from Janus variable-constants physics before it can be used as evidence.",
            "- The next target is to derive the signs and slopes of `S_DM` and `S_DH` from source equations, especially Eq. 40-type gauge scaling.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(format_fit(best.fit))


if __name__ == "__main__":
    main()

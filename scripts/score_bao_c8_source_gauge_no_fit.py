from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion
from janus_lab.bao import janus_bao_prediction
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import FitResult, chi_square


REPORT_PATH = Path("outputs/reports/janus_bao_c8_source_gauge_no_fit_score.md")
CSV_PATH = Path("outputs/reports/janus_bao_c8_source_gauge_no_fit_predictions.csv")
SN_Q0 = -0.087


@dataclass(frozen=True)
class SourceGaugeCandidate:
    name: str
    dm_power: float
    dh_power: float
    source_rule: str


@dataclass(frozen=True)
class SourceGaugeFit:
    candidate: SourceGaugeCandidate
    scale: float
    chi2: float
    prediction: np.ndarray

    @property
    def fit(self) -> FitResult:
        return FitResult(
            name=f"C8 no-fit source gauge, {self.candidate.name}",
            chi2=self.chi2,
            n_data=len(self.prediction),
            n_params=1,
            params={
                "q0": SN_Q0,
                "scale": self.scale,
                "dm_power": self.candidate.dm_power,
                "dh_power": self.candidate.dh_power,
            },
        )


CANDIDATES = [
    SourceGaugeCandidate(
        name="base_constant_ruler",
        dm_power=0.0,
        dh_power=0.0,
        source_rule="M18 open distance plus constant BAO ruler",
    ),
    SourceGaugeCandidate(
        name="common_sqrt_a",
        dm_power=-0.5,
        dh_power=-0.5,
        source_rule="X2026 Eq. 40 inverse-speed gauge applied to both BAO ratios",
    ),
    SourceGaugeCandidate(
        name="radial_sqrt_a",
        dm_power=0.0,
        dh_power=-0.5,
        source_rule="X2026 Eq. 40 inverse-speed gauge applied only to radial BAO",
    ),
    SourceGaugeCandidate(
        name="transverse_sqrt_a",
        dm_power=-0.5,
        dh_power=0.0,
        source_rule="X2026 Eq. 40 gauge applied only to transverse BAO",
    ),
]


def candidate_shape(candidate: SourceGaugeCandidate) -> np.ndarray:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(SN_Q0)
    values = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        dm = janus_bao_prediction(float(z), "DM_over_rs", model, scale=1.0) * (1.0 + z) ** candidate.dm_power
        dh = janus_bao_prediction(float(z), "DH_over_rs", model, scale=1.0) * (1.0 + z) ** candidate.dh_power
        dv = np.cbrt(float(z) * dm**2 * dh)
        if quantity == "DM_over_rs":
            values.append(dm)
        elif quantity == "DH_over_rs":
            values.append(dh)
        elif quantity == "DV_over_rs":
            values.append(dv)
        else:
            raise ValueError(f"Unsupported BAO quantity: {quantity}")
    return np.asarray(values, dtype=float)


def fit_candidate(candidate: SourceGaugeCandidate) -> SourceGaugeFit:
    dataset = load_desi_bao()
    shape = candidate_shape(candidate)
    inv_cov = np.linalg.inv(dataset.covariance)
    scale = float(shape @ inv_cov @ dataset.value / (shape @ inv_cov @ shape))
    prediction = scale * shape
    chi2 = chi_square(dataset.value - prediction, covariance=dataset.covariance)
    return SourceGaugeFit(candidate=candidate, scale=scale, chi2=chi2, prediction=prediction)


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
    fits = [fit_candidate(candidate) for candidate in CANDIDATES]
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
        "# Janus BAO C8 Source-Gauge No-Fit Score",
        "",
        "C8 uses no data-fitted shape parameters:",
        "",
        "- `q0` is fixed to the M18 supernova value `-0.087`;",
        "- powers are fixed from source gauge logic, especially X2026 Eq. 40;",
        "- only one global BAO normalization is fitted because `H0*r_d` is not fixed here.",
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
            "## Source Rules",
            "",
            "| candidate | source rule |",
            "|---|---|",
            *[f"| {candidate.name} | {candidate.source_rule} |" for candidate in CANDIDATES],
            "",
            f"Best predictions CSV: `{CSV_PATH}`",
            "",
            "## Reading",
            "",
            "- These are admissible source-gauge tests, not fitted rescue forms.",
            "- The direct Eq. 40 candidates do not yet solve DESI BAO.",
            "- Therefore C7 remains only a diagnostic target: its anisotropy must be derived before it can be claimed.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(format_fit(best.fit))


if __name__ == "__main__":
    main()

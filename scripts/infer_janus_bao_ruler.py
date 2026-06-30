from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion
from janus_lab.bao import janus_bao_prediction_vector
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import FitResult, weighted_linear_fit


QUANTITIES = ["DM_over_rs", "DH_over_rs", "DV_over_rs"]


@dataclass(frozen=True)
class RulerFit:
    name: str
    q0: float
    fit: FitResult
    coeffs: np.ndarray
    prediction: np.ndarray
    columns: list[str]


def design_single_polynomial(base: np.ndarray, z: np.ndarray, degree: int) -> tuple[np.ndarray, list[str]]:
    columns = [f"s_z{k}" for k in range(degree + 1)]
    design = np.column_stack([base * z**k for k in range(degree + 1)])
    return design, columns


def design_by_quantity(
    base: np.ndarray,
    z: np.ndarray,
    quantities: np.ndarray,
    degree: int,
) -> tuple[np.ndarray, list[str]]:
    columns: list[str] = []
    blocks: list[np.ndarray] = []
    for quantity in QUANTITIES:
        mask = (quantities == quantity).astype(float)
        if not np.any(mask):
            continue
        for power in range(degree + 1):
            columns.append(f"{quantity}_z{power}")
            blocks.append(base * mask * z**power)
    return np.column_stack(blocks), columns


def fit_ruler_family(q0: float, family: str, degree: int) -> RulerFit:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    base = janus_bao_prediction_vector(dataset, model, scale=1.0)

    if family == "single":
        design, columns = design_single_polynomial(base, dataset.z, degree)
        name = f"Janus q0={q0:.4f} single scale poly{degree}"
    elif family == "by_quantity":
        design, columns = design_by_quantity(base, dataset.z, dataset.quantity, degree)
        name = f"Janus q0={q0:.4f} quantity scale poly{degree}"
    else:
        raise ValueError(f"Unknown family: {family}")

    coeffs, prediction, chi2 = weighted_linear_fit(design, dataset.value, dataset.covariance)
    fit = FitResult(
        name=name,
        chi2=chi2,
        n_data=len(dataset.value),
        n_params=len(coeffs) + 1,
        params={"q0": q0},
    )
    return RulerFit(name=name, q0=q0, fit=fit, coeffs=coeffs, prediction=prediction, columns=columns)


def correction_at_z(fit: RulerFit, z: float, quantity: str) -> float:
    if "single scale" in fit.name:
        return float(sum(coef * z**power for power, coef in enumerate(fit.coeffs)))

    value = 0.0
    for coef, column in zip(fit.coeffs, fit.columns):
        column_quantity, _, z_power = column.rpartition("_z")
        if column_quantity == quantity:
            value += coef * z ** int(z_power)
    return float(value)


def fit_log_power_law(points: list[tuple[float, float]]) -> tuple[float, float]:
    """Fit scale ~= amplitude * (1+z)^power in log space."""

    x = np.asarray([np.log1p(z) for z, _ in points], dtype=float)
    y = np.asarray([np.log(scale) for _, scale in points], dtype=float)
    design = np.column_stack([np.ones_like(x), x])
    coeffs, *_ = np.linalg.lstsq(design, y, rcond=None)
    return float(np.exp(coeffs[0])), float(coeffs[1])


def fit_sqrt_a_family(q0: float) -> RulerFit:
    """Fit quantity constants assuming effective scale proportional to sqrt(a)."""

    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    base = janus_bao_prediction_vector(dataset, model, scale=1.0)
    sqrt_a = 1.0 / np.sqrt(1.0 + dataset.z)

    blocks = []
    columns = []
    for quantity in QUANTITIES:
        mask = (dataset.quantity == quantity).astype(float)
        if np.any(mask):
            columns.append(f"{quantity}_sqrt_a")
            blocks.append(base * sqrt_a * mask)
    design = np.column_stack(blocks)
    coeffs, prediction, chi2 = weighted_linear_fit(design, dataset.value, dataset.covariance)
    fit = FitResult(
        name=f"Janus q0={q0:.4f} quantity scale sqrt(a)",
        chi2=chi2,
        n_data=len(dataset.value),
        n_params=len(coeffs) + 1,
        params={"q0": q0},
    )
    return RulerFit(name=fit.name, q0=q0, fit=fit, coeffs=coeffs, prediction=prediction, columns=columns)


def format_fit(fit: RulerFit) -> str:
    coeff_text = ", ".join(
        f"{name}={value:.6g}" for name, value in zip(fit.columns, fit.coeffs)
    )
    return (
        f"| {fit.name} | {fit.fit.chi2:.3f} | {fit.fit.dof} | "
        f"{fit.fit.chi2_per_dof:.3f} | {fit.fit.aic:.3f} | {fit.fit.bic:.3f} | {coeff_text} |"
    )


def main() -> None:
    ensure_default_data()
    dataset = load_desi_bao()
    report_dir = Path("outputs/reports")
    report_dir.mkdir(parents=True, exist_ok=True)

    q0_grid = np.array([-0.001, -0.003, -0.005, -0.01, -0.02, -0.03, -0.05, -0.087])
    fits: list[RulerFit] = []
    for q0 in q0_grid:
        for degree in [0, 1, 2, 3]:
            fits.append(fit_ruler_family(float(q0), "single", degree))
        for degree in [0, 1]:
            fits.append(fit_ruler_family(float(q0), "by_quantity", degree))

    best = sorted(fits, key=lambda item: item.fit.aic)[:12]
    best_janus_like = [fit for fit in best if fit.q0 <= -0.02]

    required_rows = []
    reference = fit_ruler_family(-0.087, "by_quantity", 1)
    sqrt_a_reference = fit_sqrt_a_family(-0.087)
    for z, observed, quantity, predicted in zip(
        dataset.z, dataset.value, dataset.quantity, reference.prediction
    ):
        required_rows.append(
            [
                z,
                quantity,
                observed,
                predicted,
                observed - predicted,
                correction_at_z(reference, float(z), str(quantity)),
            ]
        )

    power_points: dict[str, list[tuple[float, float]]] = {quantity: [] for quantity in QUANTITIES}
    for z, quantity, _, _, _, effective_scale in required_rows:
        power_points[str(quantity)].append((float(z), float(effective_scale)))

    power_lines = []
    for quantity in ["DM_over_rs", "DH_over_rs"]:
        amplitude, power = fit_log_power_law(power_points[quantity])
        power_lines.append(
            f"| {quantity} | {amplitude:.4f} | {power:.4f} |"
        )

    csv_output = report_dir / "janus_bao_required_ruler.csv"
    with csv_output.open("w", encoding="utf-8") as handle:
        handle.write("z,quantity,observed,predicted,residual,effective_scale\n")
        for row in required_rows:
            handle.write(
                f"{row[0]:.8g},{row[1]},{row[2]:.10g},{row[3]:.10g},{row[4]:.10g},{row[5]:.10g}\n"
            )

    lines = [
        "# Janus BAO Ruler Inference",
        "",
        "Working axiom: Janus is true. Therefore BAO mismatch is interpreted as a constraint on the missing Janus BAO ruler/observable map, not as immediate rejection.",
        "",
        "The fitted correction multiplies the Janus BAO base prediction. A single polynomial means one effective scale for all BAO quantities. A quantity polynomial allows different transverse/radial/effective corrections.",
        "",
        "## Best Correction Families",
        "",
        "| Model | chi2 | dof | chi2/dof | AIC | BIC | coefficients |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_fit(fit) for fit in best],
        "",
        "## Best Fits With q0 <= -0.02",
        "",
        "| Model | chi2 | dof | chi2/dof | AIC | BIC | coefficients |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_fit(fit) for fit in best_janus_like[:8]],
        "",
        "## Reference q0=-0.087 Quantity-Linear Effective Scales",
        "",
        f"CSV: `{csv_output}`",
        "",
        "| z | quantity | effective scale | residual |",
        "|---:|---|---:|---:|",
    ]

    for z, quantity, _, _, residual, effective_scale in required_rows:
        lines.append(f"| {z:.3f} | {quantity} | {effective_scale:.4f} | {residual:.4f} |")

    lines.extend(
        [
            "",
            "## Gauge-Law Clue",
            "",
            "The reference effective scales are well approximated by `scale_eff ~= A * (1+z)^p`, with exponents close to `-1/2` for the transverse and radial measurements.",
            "",
            "| quantity | amplitude A | power p |",
            "|---|---:|---:|",
            *power_lines,
            "",
            "A constrained `sqrt(a) = (1+z)^-1/2` quantity-dependent family gives:",
            "",
            "| Model | chi2 | dof | chi2/dof | AIC | BIC | coefficients |",
            "|---|---:|---:|---:|---:|---:|---|",
            format_fit(sqrt_a_reference),
            "",
            "## Reading",
            "",
            "- A single global ruler is not enough.",
            "- A single redshift polynomial improves but remains poor.",
            "- A quantity-dependent linear ruler is dramatically better and prefers the published supernova value q0 ~= -0.087 in this grid.",
            "- The inferred exponents are close to the variable-constants gauge exponent sqrt(a), but the exact sqrt(a) toy family is not sufficient by itself.",
            "- The fit is still phenomenological. It becomes evidence only if the DM/DH anisotropic ruler can be derived from Janus physics, especially from the variable-constants regime.",
        ]
    )

    report_output = report_dir / "janus_bao_ruler_inference.md"
    report_output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {report_output}")
    print(f"Wrote {csv_output}")
    print("\n".join(lines[:20]))


if __name__ == "__main__":
    main()

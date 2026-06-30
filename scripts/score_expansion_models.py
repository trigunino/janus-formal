from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab import (
    JanusExpansion,
    distance_modulus,
    e_cpl,
    e_lcdm,
    janus_distance_modulus_proxy,
)
from janus_lab.bao import (
    bao_prediction_vector,
    janus_bao_prediction_vector,
    planck_like_scale,
)
from janus_lab.data import ensure_default_data, load_desi_bao, load_pantheon_diag
from janus_lab.statistics import FitResult, chi_square, fit_additive_offset, grid_search


def score_bao(name: str, bao_predictor, n_shape_params: int, grid_scale: np.ndarray) -> FitResult:
    dataset = load_desi_bao()

    def scorer(params: dict[str, float]) -> float:
        prediction = bao_predictor(dataset, params["scale"])
        return chi_square(dataset.value - prediction, covariance=dataset.covariance)

    params, chi2 = grid_search(scorer, {"scale": grid_scale})
    return FitResult(
        name=f"{name} / DESI DR2 BAO",
        chi2=chi2,
        n_data=len(dataset.value),
        n_params=n_shape_params + 1,
        params=params,
    )


def score_sn(name: str, predictor, n_shape_params: int) -> FitResult:
    dataset = load_pantheon_diag()
    predicted = predictor(dataset.z)
    offset = fit_additive_offset(dataset.mu, predicted, dataset.sigma_mu)
    chi2 = chi_square(dataset.mu - (predicted + offset), sigma=dataset.sigma_mu)
    return FitResult(
        name=f"{name} / Pantheon+ diag",
        chi2=chi2,
        n_data=len(dataset.z),
        n_params=n_shape_params + 1,
        params={"mu_offset": offset},
    )


def combine_results(name: str, bao: FitResult, sn: FitResult) -> FitResult:
    """Combine independent BAO and diagonal-SN scores for the same model."""

    params = {
        **{f"bao_{key}": value for key, value in bao.params.items()},
        **{f"sn_{key}": value for key, value in sn.params.items()},
    }
    return FitResult(
        name=f"{name} / DESI BAO + Pantheon+ diag",
        chi2=bao.chi2 + sn.chi2,
        n_data=bao.n_data + sn.n_data,
        n_params=bao.n_params + sn.n_params,
        params=params,
    )


def format_result(result: FitResult) -> str:
    params = ", ".join(f"{key}={value:.6g}" for key, value in result.params.items())
    return (
        f"| {result.name} | {result.chi2:.3f} | {result.dof} | "
        f"{result.chi2_per_dof:.3f} | {result.aic:.3f} | {result.bic:.3f} | {params} |"
    )


def main() -> None:
    ensure_default_data()
    report_dir = Path("outputs/reports")
    report_dir.mkdir(parents=True, exist_ok=True)

    default_scale = planck_like_scale()
    grid_scale = np.linspace(default_scale * 0.92, default_scale * 1.08, 129)

    models = []

    # Lambda-CDM: fit only Omega_m coarsely. BAO-only still fits the scale.
    for omega_m in [0.20, 0.25, 0.30, 0.315, 0.35, 0.40]:
        e_func = lambda z, om=omega_m: e_lcdm(z, omega_m=om)
        sn_predictor = lambda z, f=e_func: distance_modulus(z, f, h0=70.0, samples=768)
        bao_predictor = lambda dataset, scale, f=e_func: bao_prediction_vector(
            dataset, f, scale=scale, samples=768
        )
        models.append((f"Lambda-CDM Om={omega_m:.3f}", bao_predictor, sn_predictor, 1))

    # CPL: deliberately small grid for first-pass evidence mapping.
    for w0 in [-1.1, -1.0, -0.9, -0.8]:
        for wa in [-1.0, -0.5, 0.0, 0.5]:
            label = f"CPL w0={w0:.1f} wa={wa:.1f}"
            e_func = lambda z, w0=w0, wa=wa: e_cpl(z, omega_m=0.315, w0=w0, wa=wa)
            sn_predictor = lambda z, f=e_func: distance_modulus(z, f, h0=70.0, samples=768)
            bao_predictor = lambda dataset, scale, f=e_func: bao_prediction_vector(
                dataset, f, scale=scale, samples=768
            )
            models.append((label, bao_predictor, sn_predictor, 3))

    # Janus: q0 is the one-parameter SN relation used in the 2018 paper.
    for q0 in [-0.03, -0.05, -0.07, -0.087, -0.10, -0.12, -0.14, -0.16, -0.18, -0.20]:
        janus = JanusExpansion.from_q0(q0)
        label = f"Janus q0={q0:.3f}"
        sn_predictor = lambda z, q0=q0: janus_distance_modulus_proxy(z, q0=q0)
        bao_predictor = lambda dataset, scale, m=janus: janus_bao_prediction_vector(
            dataset, m, scale=scale
        )
        models.append((label, bao_predictor, sn_predictor, 1))

    bao_results = [
        score_bao(label, bao_predictor, n_params, grid_scale)
        for label, bao_predictor, _, n_params in models
    ]
    sn_results = [
        score_sn(label, sn_predictor, n_params)
        for label, _, sn_predictor, n_params in models
    ]
    combined_results = [
        combine_results(label, bao, sn)
        for (label, _, _, _), bao, sn in zip(models, bao_results, sn_results)
    ]

    best_bao = sorted(bao_results, key=lambda result: result.aic)[:10]
    best_sn = sorted(sn_results, key=lambda result: result.aic)[:10]
    best_combined = sorted(combined_results, key=lambda result: result.aic)[:10]
    best_janus_bao = sorted(
        [result for result in bao_results if result.name.startswith("Janus")],
        key=lambda result: result.aic,
    )[:5]
    best_janus_sn = sorted(
        [result for result in sn_results if result.name.startswith("Janus")],
        key=lambda result: result.aic,
    )[:5]
    best_janus_combined = sorted(
        [result for result in combined_results if result.name.startswith("Janus")],
        key=lambda result: result.aic,
    )[:5]

    lines = [
        "# Baseline Expansion Scores",
        "",
        "Exploratory first pass. Pantheon+ uses diagonal errors only; DESI DR2 uses the published Gaussian BAO covariance.",
        "",
        "## Best DESI DR2 BAO Scores",
        "",
        "| Model / data | chi2 | dof | chi2/dof | AIC | BIC | fitted nuisance |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_result(result) for result in best_bao],
        "",
        "## Best Janus DESI DR2 BAO Scores",
        "",
        "| Model / data | chi2 | dof | chi2/dof | AIC | BIC | fitted nuisance |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_result(result) for result in best_janus_bao],
        "",
        "## Best Pantheon+ Diagonal Scores",
        "",
        "| Model / data | chi2 | dof | chi2/dof | AIC | BIC | fitted nuisance |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_result(result) for result in best_sn],
        "",
        "## Best Janus Pantheon+ Diagonal Scores",
        "",
        "| Model / data | chi2 | dof | chi2/dof | AIC | BIC | fitted nuisance |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_result(result) for result in best_janus_sn],
        "",
        "## Best Combined Scores",
        "",
        "| Model / data | chi2 | dof | chi2/dof | AIC | BIC | fitted nuisance |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_result(result) for result in best_combined],
        "",
        "## Best Janus Combined Scores",
        "",
        "| Model / data | chi2 | dof | chi2/dof | AIC | BIC | fitted nuisance |",
        "|---|---:|---:|---:|---:|---:|---|",
        *[format_result(result) for result in best_janus_combined],
        "",
        "## Interpretation Guardrails",
        "",
        "- This is not yet a proof. It is a smoke test for expansion histories.",
        "- BAO-only mainly constrains c/(H0*r_d), so the scale is fitted as a nuisance.",
        "- Pantheon+ must be rerun with the full covariance before any strong claim.",
        "- The next important test is the combined DESI+Pantheon likelihood with shared shape parameters.",
    ]

    output = report_dir / "baseline_expansion_scores.md"
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {output}")
    print("\n".join(lines[:18]))


if __name__ == "__main__":
    main()

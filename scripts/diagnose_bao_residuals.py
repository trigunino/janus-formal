from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion, e_lcdm
from janus_lab.bao import bao_prediction_vector, janus_bao_prediction_vector, planck_like_scale
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import chi_square, grid_search


def best_scale(dataset, predictor) -> tuple[float, float, np.ndarray]:
    default = planck_like_scale()
    grid = np.linspace(default * 0.7, default * 1.3, 241)

    def scorer(params: dict[str, float]) -> float:
        prediction = predictor(params["scale"])
        return chi_square(dataset.value - prediction, covariance=dataset.covariance)

    params, score = grid_search(scorer, {"scale": grid})
    prediction = predictor(params["scale"])
    return params["scale"], score, prediction


def main() -> None:
    ensure_default_data()
    dataset = load_desi_bao()
    out_dir = Path("outputs/reports")
    out_dir.mkdir(parents=True, exist_ok=True)

    lcdm_func = lambda z: e_lcdm(z, omega_m=0.300)
    lcdm_scale, lcdm_chi2, lcdm_pred = best_scale(
        dataset,
        lambda scale: bao_prediction_vector(dataset, lcdm_func, scale=scale, samples=768),
    )

    janus = JanusExpansion.from_q0(-0.030)
    janus_scale, janus_chi2, janus_pred = best_scale(
        dataset,
        lambda scale: janus_bao_prediction_vector(dataset, janus, scale=scale),
    )

    output = out_dir / "bao_residuals.csv"
    rows = np.column_stack(
        [
            dataset.z,
            dataset.value,
            lcdm_pred,
            dataset.value - lcdm_pred,
            janus_pred,
            dataset.value - janus_pred,
        ]
    )
    header = "z,observed,lcdm_pred,lcdm_residual,janus_pred,janus_residual"
    np.savetxt(output, rows, delimiter=",", header=header, comments="")
    print(f"Wrote {output}")
    print(f"LCDM scale={lcdm_scale:.6g} chi2={lcdm_chi2:.3f}")
    print(f"Janus scale={janus_scale:.6g} chi2={janus_chi2:.3f}")


if __name__ == "__main__":
    main()

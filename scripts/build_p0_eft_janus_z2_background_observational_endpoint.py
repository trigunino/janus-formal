from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab import JanusExpansion, distance_modulus, e_cpl, e_lcdm
from janus_lab.bao import bao_prediction_vector
from janus_lab.data import ensure_default_data, load_desi_bao, load_pantheon_full_cov
from janus_lab.statistics import chi_square
from scripts.build_p0_eft_janus_z2_alpha_observational_fit_gate import (
    _fit_bao_scale,
    _profile_offset_and_chi2_from_precision,
    build_payload as build_alpha_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_background_observational_endpoint.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_background_observational_endpoint.md"


def _score_standard_background(
    label: str,
    e_func,
    sn_z: np.ndarray,
    sn_mu: np.ndarray,
    sn_precision: np.ndarray,
    sn_precision_ones: np.ndarray,
    sn_ones_precision_ones: float,
    bao,
    samples: int = 384,
) -> dict:
    sn_pred = np.asarray(distance_modulus(sn_z, e_func, h0=70.0, samples=samples), dtype=float)
    mu_offset, chi2_sn = _profile_offset_and_chi2_from_precision(
        sn_mu,
        sn_pred,
        sn_precision,
        sn_precision_ones,
        sn_ones_precision_ones,
    )
    bao_basis = bao_prediction_vector(bao, e_func, scale=1.0, samples=samples)
    bao_scale, chi2_bao = _fit_bao_scale(bao.value, bao_basis, bao.covariance)
    return {
        "label": label,
        "chi2_sn_full_cov": float(chi2_sn),
        "chi2_bao": float(chi2_bao),
        "chi2_combined": float(chi2_sn + chi2_bao),
        "mu_offset_full_cov": float(mu_offset),
        "bao_scale": float(bao_scale),
    }


def build_payload() -> dict:
    ensure_default_data()
    alpha_payload = build_alpha_payload()
    sn = load_pantheon_full_cov()
    bao = load_desi_bao()

    sn_precision = np.linalg.inv(sn.covariance)
    sn_precision_ones = sn_precision @ np.ones(len(sn.mu), dtype=float)
    sn_ones_precision_ones = float(np.sum(sn_precision_ones))

    lcdm_rows = []
    for omega_m in np.linspace(0.2, 0.4, 41):
        lcdm_rows.append(
            {
                "omega_m": float(omega_m),
                **_score_standard_background(
                    f"LCDM omega_m={omega_m:.3f}",
                    lambda z, om=float(omega_m): e_lcdm(z, omega_m=om),
                    sn.z,
                    sn.mu,
                    sn_precision,
                    sn_precision_ones,
                    sn_ones_precision_ones,
                    bao,
                ),
            }
        )
    best_lcdm = min(lcdm_rows, key=lambda row: row["chi2_combined"])

    cpl_rows = []
    for w0 in np.linspace(-1.2, -0.7, 11):
        for wa in np.linspace(-1.0, 0.5, 7):
            cpl_rows.append(
                {
                    "w0": float(w0),
                    "wa": float(wa),
                    **_score_standard_background(
                        f"CPL w0={w0:.3f} wa={wa:.3f}",
                        lambda z, w0=float(w0), wa=float(wa): e_cpl(
                            z, omega_m=0.315, w0=w0, wa=wa
                        ),
                        sn.z,
                        sn.mu,
                        sn_precision,
                        sn_precision_ones,
                        sn_ones_precision_ones,
                        bao,
                    ),
                }
            )
    best_cpl = min(cpl_rows, key=lambda row: row["chi2_combined"])

    janus = alpha_payload["best_fit"]["SN_full_cov_plus_BAO"]
    best_baseline = min(
        [
            {"family": "LCDM", **best_lcdm},
            {"family": "CPL", **best_cpl},
        ],
        key=lambda row: row["chi2_combined"],
    )

    janus_vs_best = float(janus["chi2"] - best_baseline["chi2_combined"])
    if janus["at_grid_boundary"] and janus_vs_best > 0.0:
        verdict = "background_observational_no_go_for_interior_janus_sector"
    elif janus_vs_best <= 0.0:
        verdict = "janus_background_competitive_on_current_dataset_set"
    else:
        verdict = "background_observational_inconclusive_requires_more_data"

    return {
        "status": "janus-z2-background-observational-endpoint",
        "datasets": {
            "SN": "Pantheon+ full covariance",
            "BAO": "DESI DR2 Gaussian BAO covariance",
            "Hz": "not_available_locally_not_used",
        },
        "janus_endpoint": janus,
        "best_baselines": {
            "LCDM": best_lcdm,
            "CPL": best_cpl,
        },
        "best_baseline_family": best_baseline["family"],
        "delta_chi2_janus_minus_best_baseline": janus_vs_best,
        "interior_janus_sector_survives": bool(
            (not janus["at_grid_boundary"]) and (janus_vs_best <= 0.0)
        ),
        "gr_limit_edge_preferred": bool(janus["at_grid_boundary"]),
        "continuation_to_branch_3_recommended": bool(
            (not janus["at_grid_boundary"]) and (janus_vs_best <= 0.0)
        ),
        "verdict": verdict,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    janus = payload["janus_endpoint"]
    lcdm = payload["best_baselines"]["LCDM"]
    cpl = payload["best_baselines"]["CPL"]
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Background Observational Endpoint",
                "",
                f"Verdict: `{payload['verdict']}`",
                f"Best baseline family: `{payload['best_baseline_family']}`",
                f"Delta chi2 Janus - best baseline: `{payload['delta_chi2_janus_minus_best_baseline']:.6g}`",
                f"GR-limit edge preferred: `{payload['gr_limit_edge_preferred']}`",
                f"Continue to branch 3: `{payload['continuation_to_branch_3_recommended']}`",
                "",
                "## Janus endpoint",
                "",
                f"- q0: `{janus['q0']:.6g}`",
                f"- u0: `{janus['u0']:.6g}`",
                f"- chi2 combined: `{janus['chi2']:.6g}`",
                f"- grid boundary: `{janus['at_grid_boundary']}`",
                "",
                "## Best LCDM",
                "",
                f"- omega_m: `{lcdm['omega_m']:.6g}`",
                f"- chi2 combined: `{lcdm['chi2_combined']:.6g}`",
                "",
                "## Best CPL",
                "",
                f"- w0: `{cpl['w0']:.6g}`",
                f"- wa: `{cpl['wa']:.6g}`",
                f"- chi2 combined: `{cpl['chi2_combined']:.6g}`",
                "",
                "H(z) / cosmic chronometers are not available locally, so the background endpoint is "
                "defined on Pantheon+ full covariance plus DESI DR2 BAO only.",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

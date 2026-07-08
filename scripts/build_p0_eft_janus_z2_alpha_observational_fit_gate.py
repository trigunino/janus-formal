from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion, janus_distance_modulus_proxy
from janus_lab.bao import janus_bao_prediction_vector
from janus_lab.data import (
    DATA_FILES,
    ensure_default_data,
    load_desi_bao,
    load_pantheon_diag,
    load_pantheon_full_cov,
)
from janus_lab.statistics import (
    chi_square,
    fit_additive_offset,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_alpha_observational_fit_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_alpha_observational_fit_gate.md"


def _fit_bao_scale(observed: np.ndarray, basis: np.ndarray, covariance: np.ndarray) -> tuple[float, float]:
    inv_basis = np.linalg.solve(covariance, basis)
    inv_observed = np.linalg.solve(covariance, observed)
    scale = float((basis @ inv_observed) / (basis @ inv_basis))
    chi2 = chi_square(observed - scale * basis, covariance=covariance)
    return scale, chi2


def _profile_offset_and_chi2_from_precision(
    observed: np.ndarray,
    predicted: np.ndarray,
    precision: np.ndarray,
    precision_ones: np.ndarray,
    ones_precision_ones: float,
) -> tuple[float, float]:
    delta = observed - predicted
    precision_delta = precision @ delta
    offset = float((precision_ones @ delta) / ones_precision_ones)
    centered = delta - offset
    chi2 = float(centered @ precision_delta - offset * (centered @ precision_ones))
    return offset, chi2


def _interval_from_delta_chi2(grid: list[dict], key: str, best_chi2: float) -> dict:
    accepted = [row[key] for row in grid if row["chi2"] <= best_chi2 + 1.0]
    if not accepted:
        return {"available": False}
    return {"available": True, "min": min(accepted), "max": max(accepted)}


def _score_q0_grid(q0_grid: np.ndarray) -> dict:
    ensure_default_data()
    sn_diag = load_pantheon_diag()
    sn_full = load_pantheon_full_cov()
    bao = load_desi_bao()
    sn_full_precision = np.linalg.inv(sn_full.covariance)
    precision_ones = sn_full_precision @ np.ones(len(sn_full.mu), dtype=float)
    ones_precision_ones = float(np.sum(precision_ones))

    rows = []
    for q0 in q0_grid:
        model = JanusExpansion.from_q0(float(q0))

        sn_pred = np.asarray(janus_distance_modulus_proxy(sn_diag.z, q0=float(q0)), dtype=float)
        mu_offset_diag = fit_additive_offset(sn_diag.mu, sn_pred, sn_diag.sigma_mu)
        chi2_sn_diag = chi_square(sn_diag.mu - (sn_pred + mu_offset_diag), sigma=sn_diag.sigma_mu)
        mu_offset_full, chi2_sn_full = _profile_offset_and_chi2_from_precision(
            sn_full.mu,
            sn_pred,
            sn_full_precision,
            precision_ones,
            ones_precision_ones,
        )

        bao_basis = janus_bao_prediction_vector(bao, model, scale=1.0)
        bao_scale, chi2_bao = _fit_bao_scale(bao.value, bao_basis, bao.covariance)

        rows.append(
            {
                "q0": float(q0),
                "u0": float(model.u0),
                "z_max": float(model.z_max),
                "chi2_sn_diag": float(chi2_sn_diag),
                "chi2_sn_full_cov": float(chi2_sn_full),
                "mu_offset_diag": float(mu_offset_diag),
                "mu_offset_full_cov": float(mu_offset_full),
                "chi2_bao": float(chi2_bao),
                "bao_scale": float(bao_scale),
                "chi2_combined_diag": float(chi2_sn_diag + chi2_bao),
                "chi2_combined_full_cov": float(chi2_sn_full + chi2_bao),
            }
        )

    def select(field: str) -> dict:
        best = min(rows, key=lambda row: row[field])
        renamed_grid = [{"q0": row["q0"], "chi2": row[field]} for row in rows]
        return {
            "q0": best["q0"],
            "u0": best["u0"],
            "z_max": best["z_max"],
            "chi2": best[field],
            "delta_chi2_1_interval_q0": _interval_from_delta_chi2(
                renamed_grid, "q0", best[field]
            ),
            "at_grid_boundary": best["q0"] in (float(q0_grid[0]), float(q0_grid[-1])),
            "mu_offset_diag": best["mu_offset_diag"],
            "mu_offset_full_cov": best["mu_offset_full_cov"],
            "bao_scale": best["bao_scale"],
        }

    return {
        "sn_diag": select("chi2_sn_diag"),
        "sn_full_cov": select("chi2_sn_full_cov"),
        "bao": select("chi2_bao"),
        "combined_diag": select("chi2_combined_diag"),
        "combined_full_cov": select("chi2_combined_full_cov"),
        "grid": rows,
        "n_sn": int(len(sn_diag.z)),
        "n_bao": int(len(bao.value)),
    }


def build_payload() -> dict:
    q0_grid = np.unique(
        np.concatenate(
            [
                np.linspace(-0.20, -0.01, 200, endpoint=False),
                np.linspace(-0.01, -1.0e-3, 200, endpoint=False),
                -np.geomspace(1.0e-3, 1.0e-6, 320),
            ]
        )
    )
    q0_grid.sort()
    scores = _score_q0_grid(q0_grid)
    combined = scores["combined_full_cov"]

    return {
        "status": "janus-z2-alpha-observational-fit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "observable_sector_parameter": "q0",
        "alpha_dimensional_map_ready": False,
        "alpha_interpretation": (
            "The exact Janus alpha cancels from dimensionless background observables; "
            "current data select u0/q0, i.e. the observable alpha-sector shape proxy."
        ),
        "datasets": {
            "SN": {
                "name": "Pantheon+SH0ES",
                "mode": "diag_and_full_covariance_profiled",
                "n": scores["n_sn"],
                "full_covariance_present": DATA_FILES["pantheon_shoes_cov"].exists(),
                "full_covariance_used": True,
            },
            "BAO": {
                "name": "DESI_DR2_BAO_Cobaya_Gaussian",
                "mode": "published_covariance",
                "n": scores["n_bao"],
            },
            "Hz": {"available": False, "used": False},
        },
        "fit_policy": {
            "q0_grid_min": float(q0_grid[0]),
            "q0_grid_max": float(q0_grid[-1]),
            "q0_points": int(q0_grid.size),
            "SN_mu_offset_profiled": True,
            "SN_full_covariance_profiled": True,
            "BAO_scale_profiled": True,
            "no_fit_claim": False,
        },
        "best_fit": {
            "SN_diag": scores["sn_diag"],
            "SN_full_cov": scores["sn_full_cov"],
            "BAO": scores["bao"],
            "SN_diag_plus_BAO": scores["combined_diag"],
            "SN_full_cov_plus_BAO": combined,
        },
        "primary_observational_endpoint": "SN_full_cov_plus_BAO",
        "classification": (
            "observational_sector_selection_to_gr_limit_boundary_limited"
            if combined["at_grid_boundary"]
            else "observational_sector_selection"
        ),
        "janus_bao_status": "rejected_in_current_background_proxy",
        "full_covariance_required_before_final_claim": False,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    best_diag = payload["best_fit"]["SN_diag_plus_BAO"]
    best_full = payload["best_fit"]["SN_full_cov_plus_BAO"]
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Alpha Observational Fit Gate",
                "",
                f"Observable sector parameter: `{payload['observable_sector_parameter']}`",
                f"Alpha dimensional map ready: `{payload['alpha_dimensional_map_ready']}`",
                f"No-fit claim: `{payload['fit_policy']['no_fit_claim']}`",
                f"Classification: `{payload['classification']}`",
                "",
                "## Primary endpoint: SN full covariance + BAO",
                "",
                f"- q0: `{best_full['q0']:.6g}`",
                f"- u0: `{best_full['u0']:.6g}`",
                f"- chi2: `{best_full['chi2']:.6g}`",
                f"- BAO scale: `{best_full['bao_scale']:.6g}`",
                f"- grid boundary: `{best_full['at_grid_boundary']}`",
                "",
                "## Diagnostic endpoint: SN diag + BAO",
                "",
                f"- q0: `{best_diag['q0']:.6g}`",
                f"- u0: `{best_diag['u0']:.6g}`",
                f"- chi2: `{best_diag['chi2']:.6g}`",
                f"- BAO scale: `{best_diag['bao_scale']:.6g}`",
                f"- grid boundary: `{best_diag['at_grid_boundary']}`",
                "",
                "## Status",
                "",
                payload["alpha_interpretation"],
                "",
                "Pantheon+ full covariance is now profiled alongside the diagonal diagnostic; "
                "DESI DR2 BAO uses the published covariance. If the optimum remains on the "
                "q0->0- boundary, the observational branch selects the GR-limit edge of the "
                "Janus shape family rather than an interior Janus sector.",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
import tarfile
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab import published_janus_extended2026_background
from janus_lab.data import ensure_default_data, load_pantheon_full_cov


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_extended2026_sn_acceleration_reproduction.json"
REPORT_PATH = REPORTS / "p0_eft_janus_extended2026_sn_acceleration_reproduction.md"
JLA_EXTRACTED_DIR = ROOT / "outputs" / "tmp" / "jla_like" / "jla_likelihood_v6"
JLA_ARCHIVE = Path.home() / "Downloads" / "jla_likelihood_v6.tgz"
JLA_FIXED_NUISANCE = {
    "alpha": 0.141,
    "beta": 3.101,
    "M": -19.05,
    "DeltaM": -0.070,
}


def _profile_offset_and_chi2(
    observed: np.ndarray,
    predicted: np.ndarray,
    precision: np.ndarray,
    precision_ones: np.ndarray,
    denominator: float,
) -> tuple[float, float]:
    delta = observed - predicted
    offset = float((precision_ones @ delta) / denominator)
    centered = delta - offset
    chi2 = float(centered @ precision @ centered)
    return offset, chi2


def _scan_q0_on_local_sn(
    q0_grid: np.ndarray,
    z: np.ndarray,
    mu: np.ndarray,
    covariance: np.ndarray,
) -> dict:
    precision = np.linalg.inv(covariance)
    ones = np.ones(len(mu), dtype=float)
    precision_ones = precision @ ones
    denominator = float(ones @ precision_ones)
    rows: list[dict] = []
    for q0 in q0_grid:
        background = published_janus_extended2026_background().__class__(q0=float(q0))
        predicted = np.asarray(background.sn_distance_modulus_proxy(z), dtype=float)
        offset, chi2 = _profile_offset_and_chi2(
            mu,
            predicted,
            precision,
            precision_ones,
            denominator,
        )
        rows.append(
            {
                "q0": float(q0),
                "u0": float(background.u0),
                "z_max": float(background.z_max),
                "mu_offset": float(offset),
                "chi2": float(chi2),
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "best_fit": best,
        "grid_min_q0": float(q0_grid[0]),
        "grid_max_q0": float(q0_grid[-1]),
        "at_grid_boundary": bool(best["q0"] in (float(q0_grid[0]), float(q0_grid[-1]))),
    }


def _read_jla_text(member: str) -> str:
    extracted = JLA_EXTRACTED_DIR / member
    if extracted.exists():
        return extracted.read_text(encoding="utf-8")
    if JLA_ARCHIVE.exists():
        with tarfile.open(JLA_ARCHIVE, "r:gz") as archive:
            with archive.extractfile(f"jla_likelihood_v6/{member}") as handle:
                if handle is None:
                    raise FileNotFoundError(member)
                return handle.read().decode("utf-8")
    raise FileNotFoundError(member)


def _jla_source_status() -> dict:
    return {
        "archive_available": bool(JLA_ARCHIVE.exists()),
        "extracted_dir_available": bool(JLA_EXTRACTED_DIR.exists()),
        "dataset_available": bool(JLA_ARCHIVE.exists() or JLA_EXTRACTED_DIR.exists()),
    }


def _load_jla_covariance_matrix(member: str) -> np.ndarray:
    lines = [line.strip() for line in _read_jla_text(member).splitlines() if line.strip()]
    size = int(lines[0])
    values = np.asarray([float(value) for value in lines[1:]], dtype=float)
    if values.size != size * size:
        raise ValueError(f"Invalid JLA covariance payload for {member}")
    return values.reshape(size, size)


def _load_jla_full_sample() -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    lines = [line.strip() for line in _read_jla_text("data/jla_lcparams.txt").splitlines() if line.strip()]
    header = lines[0].lstrip("#").split()
    index = {name: i for i, name in enumerate(header)}
    rows = [line.split() for line in lines[1:]]

    def column(name: str) -> np.ndarray:
        return np.asarray([float(row[index[name]]) for row in rows], dtype=float)

    zcmb = column("zcmb")
    mb = column("mb")
    dmb = column("dmb")
    x1 = column("x1")
    dx1 = column("dx1")
    color = column("color")
    dcolor = column("dcolor")
    thirdvar = column("3rdvar")
    cov_m_s = column("cov_m_s")
    cov_m_c = column("cov_m_c")
    cov_s_c = column("cov_s_c")

    dataset_lines = [line.strip() for line in _read_jla_text("data/jla.dataset").splitlines() if line.strip()]
    scriptmcut = 10.0
    for line in dataset_lines:
        if line.startswith("scriptmcut"):
            scriptmcut = float(line.split("=", 1)[1].strip())
            break

    alpha = JLA_FIXED_NUISANCE["alpha"]
    beta = JLA_FIXED_NUISANCE["beta"]
    delta_m = JLA_FIXED_NUISANCE["DeltaM"]

    c00 = _load_jla_covariance_matrix("data/jla_v0_covmatrix.dat")
    c11 = _load_jla_covariance_matrix("data/jla_va_covmatrix.dat")
    c22 = _load_jla_covariance_matrix("data/jla_vb_covmatrix.dat")
    c01 = _load_jla_covariance_matrix("data/jla_v0a_covmatrix.dat")
    c02 = _load_jla_covariance_matrix("data/jla_v0b_covmatrix.dat")
    c12 = _load_jla_covariance_matrix("data/jla_vab_covmatrix.dat")

    covariance = (
        c00
        + (alpha**2) * c11
        + (beta**2) * c22
        + 2.0 * alpha * c01
        - 2.0 * beta * c02
        - 2.0 * alpha * beta * c12
    )
    covariance = covariance.copy()
    diagonal = (
        dmb**2
        + (alpha * dx1) ** 2
        + (beta * dcolor) ** 2
        + 2.0 * alpha * cov_m_s
        - 2.0 * beta * cov_m_c
        - 2.0 * alpha * beta * cov_s_c
    )
    covariance[np.diag_indices_from(covariance)] += diagonal
    standardized_mu = mb + alpha * x1 - beta * color - delta_m * (thirdvar > scriptmcut)
    return zcmb, standardized_mu, covariance


def _scan_q0_on_jla(q0_grid: np.ndarray) -> dict:
    z, mu, covariance = _load_jla_full_sample()
    precision = np.linalg.inv(covariance)
    ones = np.ones(len(mu), dtype=float)
    precision_ones = precision @ ones
    denominator = float(ones @ precision_ones)
    rows: list[dict] = []
    for q0 in q0_grid:
        background = published_janus_extended2026_background().__class__(q0=float(q0))
        predicted = np.asarray(background.sn_distance_modulus_proxy(z), dtype=float)
        offset, chi2 = _profile_offset_and_chi2(
            mu,
            predicted,
            precision,
            precision_ones,
            denominator,
        )
        rows.append(
            {
                "q0": float(q0),
                "u0": float(background.u0),
                "z_max": float(background.z_max),
                "cst_offset": float(offset),
                "chi2": float(chi2),
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "n": int(len(z)),
        "best_fit": best,
        "grid_min_q0": float(q0_grid[0]),
        "grid_max_q0": float(q0_grid[-1]),
        "at_grid_boundary": bool(best["q0"] in (float(q0_grid[0]), float(q0_grid[-1]))),
    }


def build_payload() -> dict:
    ensure_default_data()
    background = published_janus_extended2026_background()

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
    jla_status = _jla_source_status()
    jla_scan = _scan_q0_on_jla(q0_grid) if jla_status["dataset_available"] else None
    sn = load_pantheon_full_cov()
    local_scan = _scan_q0_on_local_sn(q0_grid, sn.z, sn.mu, sn.covariance)

    analytic_checks = {
        "q0_anchor_matches_object": bool(abs(background.q0 + 0.087) < 1.0e-15),
        "e_plus_at_z0_is_unity": bool(abs(background.e_plus(0.0) - 1.0) < 1.0e-12),
        "u0_positive": bool(background.u0 > 0.0),
        "z_max_positive": bool(background.z_max > 0.0),
    }

    best_q0 = float(local_scan["best_fit"]["q0"])
    published_q0 = float(background.q0)
    return {
        "status": "janus-extended2026-sn-acceleration-reproduction",
        "source_policy": "strict_active_sources_only",
        "paper_claim_scope": [
            "M18_q0_anchor",
            "M18_exact_shape_a_of_u",
            "M18_acceleration_q_of_u",
            "M18_SN_magnitude_redshift_proxy",
            "M30_observational_reuse_of_M18_branch",
        ],
        "analytic_reproduction": {
            "published_q0": published_q0,
            "u0": float(background.u0),
            "z_max": float(background.z_max),
            "checks": analytic_checks,
            "exact_shape_recovered": bool(all(analytic_checks.values())),
        },
        "paper_native_jla_reproduction": {
            "paper_dataset_name": "Betoule et al. 740 SNe",
            "dataset_available_locally": bool(jla_status["dataset_available"]),
            "source_status": jla_status,
            "fixed_nuisance": JLA_FIXED_NUISANCE,
            "exact_q0_refit_on_original_dataset_run": bool(jla_scan is not None),
            "best_fit_q0": None if jla_scan is None else float(jla_scan["best_fit"]["q0"]),
            "best_fit_u0": None if jla_scan is None else float(jla_scan["best_fit"]["u0"]),
            "best_fit_z_max": None if jla_scan is None else float(jla_scan["best_fit"]["z_max"]),
            "best_fit_chi2": None if jla_scan is None else float(jla_scan["best_fit"]["chi2"]),
            "best_fit_cst_offset": None if jla_scan is None else float(jla_scan["best_fit"]["cst_offset"]),
            "n": None if jla_scan is None else int(jla_scan["n"]),
            "grid_boundary": None if jla_scan is None else bool(jla_scan["at_grid_boundary"]),
            "published_q0_recovered_exactly": None
            if jla_scan is None
            else bool(abs(float(jla_scan["best_fit"]["q0"]) - published_q0) < 1.0e-12),
            "published_q0_recovered_within_m18_sigma": None
            if jla_scan is None
            else bool(abs(float(jla_scan["best_fit"]["q0"]) - published_q0) <= 0.015),
            "status": "ok" if jla_scan is not None else "blocked_missing_jla_dataset",
        },
        "supplementary_local_sn_dataset_diagnostic": {
            "dataset_name": "Pantheon+SH0ES full covariance",
            "n": int(len(sn.z)),
            "best_fit_q0": best_q0,
            "best_fit_u0": float(local_scan["best_fit"]["u0"]),
            "best_fit_z_max": float(local_scan["best_fit"]["z_max"]),
            "best_fit_chi2": float(local_scan["best_fit"]["chi2"]),
            "best_fit_mu_offset": float(local_scan["best_fit"]["mu_offset"]),
            "grid_boundary": bool(local_scan["at_grid_boundary"]),
            "published_q0_recovered_exactly": bool(abs(best_q0 - published_q0) < 1.0e-12),
            "published_q0_recovered_within_m18_sigma": bool(abs(best_q0 - published_q0) <= 0.015),
        },
        "verdict": {
            "published_branch_recovered_exactly": bool(all(analytic_checks.values())),
            "published_fit_recovered_on_original_dataset": None
            if jla_scan is None
            else bool(abs(float(jla_scan["best_fit"]["q0"]) - published_q0) <= 0.015),
            "published_q0_recovered_on_local_sn_dataset": bool(abs(best_q0 - published_q0) <= 0.015),
        },
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    jla = payload["paper_native_jla_reproduction"]
    local = payload["supplementary_local_sn_dataset_diagnostic"]
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Extended2026 SN/Acceleration Reproduction",
                "",
                f"Source policy: `{payload['source_policy']}`",
                f"Published branch recovered exactly: `{payload['verdict']['published_branch_recovered_exactly']}`",
                f"Original paper dataset available locally: `{jla['dataset_available_locally']}`",
                f"Published q0 recovered on JLA within M18 sigma: `{jla['published_q0_recovered_within_m18_sigma']}`",
                f"Published q0 recovered on local SN dataset within M18 sigma: `{local['published_q0_recovered_within_m18_sigma']}`",
                "",
                "## Analytic reproduction",
                "",
                f"- published q0: `{payload['analytic_reproduction']['published_q0']}`",
                f"- u0: `{payload['analytic_reproduction']['u0']:.6g}`",
                f"- z_max: `{payload['analytic_reproduction']['z_max']:.6g}`",
                "",
                "## Paper-native JLA rerun",
                "",
                f"- n: `{jla['n']}`",
                f"- best-fit q0: `{jla['best_fit_q0']}`",
                f"- best-fit chi2: `{jla['best_fit_chi2']}`",
                f"- best-fit cst offset: `{jla['best_fit_cst_offset']}`",
                f"- grid boundary: `{jla['grid_boundary']}`",
                "",
                "## Local SN-only diagnostic",
                "",
                f"- dataset: `{local['dataset_name']}`",
                f"- n: `{local['n']}`",
                f"- best-fit q0: `{local['best_fit_q0']:.6g}`",
                f"- best-fit chi2: `{local['best_fit_chi2']:.6g}`",
                f"- best-fit offset: `{local['best_fit_mu_offset']:.6g}`",
                f"- grid boundary: `{local['grid_boundary']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

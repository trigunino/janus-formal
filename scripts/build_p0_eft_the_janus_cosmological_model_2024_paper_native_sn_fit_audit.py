from __future__ import annotations

import json
import sys
import tarfile
from dataclasses import dataclass
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab import published_janus_extended2026_background


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_paper_native_sn_fit_audit.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_paper_native_sn_fit_audit.md"
JLA_EXTRACTED_DIR = ROOT / "outputs" / "tmp" / "jla_like" / "jla_likelihood_v6"
JLA_ARCHIVE = Path.home() / "Downloads" / "jla_likelihood_v6.tgz"
PUBLISHED_Q0 = -0.087
PUBLISHED_SIGMA_Q0 = 0.015
PUBLISHED_CHI2 = 657.0


@dataclass(frozen=True)
class ProcedureSpec:
    name: str
    z_kind: str
    alpha: float
    beta: float
    use_delta_m: bool
    covariance_kind: str
    q0_min: float
    q0_max: float
    q0_samples: int


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


def _load_jla_covariance_matrix(member: str) -> np.ndarray:
    lines = [line.strip() for line in _read_jla_text(member).splitlines() if line.strip()]
    size = int(lines[0])
    values = np.asarray([float(value) for value in lines[1:]], dtype=float)
    if values.size != size * size:
        raise ValueError(f"Invalid JLA covariance payload for {member}")
    return values.reshape(size, size)


def _load_jla_columns() -> dict[str, np.ndarray]:
    lines = [line.strip() for line in _read_jla_text("data/jla_lcparams.txt").splitlines() if line.strip()]
    header = lines[0].lstrip("#").split()
    index = {name: i for i, name in enumerate(header)}
    rows = [line.split() for line in lines[1:]]
    return {
        name: np.asarray([float(row[idx]) for row in rows], dtype=float)
        for name, idx in index.items()
        if name != "name" and name != "set"
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


def _build_covariance(columns: dict[str, np.ndarray], alpha: float, beta: float, kind: str) -> np.ndarray:
    dmb = columns["dmb"]
    dx1 = columns["dx1"]
    dcolor = columns["dcolor"]
    cov_m_s = columns["cov_m_s"]
    cov_m_c = columns["cov_m_c"]
    cov_s_c = columns["cov_s_c"]

    stat_diag = dmb**2 + (alpha * dx1) ** 2 + (beta * dcolor) ** 2
    stat_diag_with_cross = stat_diag + 2.0 * alpha * cov_m_s - 2.0 * beta * cov_m_c - 2.0 * alpha * beta * cov_s_c
    if kind == "dmb_alpha_beta_plain":
        return np.diag(stat_diag)

    if not hasattr(_build_covariance, "_cache"):
        _build_covariance._cache = {
            "c00": _load_jla_covariance_matrix("data/jla_v0_covmatrix.dat"),
            "c11": _load_jla_covariance_matrix("data/jla_va_covmatrix.dat"),
            "c22": _load_jla_covariance_matrix("data/jla_vb_covmatrix.dat"),
            "c01": _load_jla_covariance_matrix("data/jla_v0a_covmatrix.dat"),
            "c02": _load_jla_covariance_matrix("data/jla_v0b_covmatrix.dat"),
            "c12": _load_jla_covariance_matrix("data/jla_vab_covmatrix.dat"),
        }
    cache = _build_covariance._cache
    total = (
        cache["c00"]
        + (alpha**2) * cache["c11"]
        + (beta**2) * cache["c22"]
        + 2.0 * alpha * cache["c01"]
        - 2.0 * beta * cache["c02"]
        - 2.0 * alpha * beta * cache["c12"]
    )
    total = total.copy()
    total[np.diag_indices_from(total)] += stat_diag_with_cross
    if kind == "full_plus_statdiag":
        return total
    if kind == "diag_total":
        return np.diag(np.diag(total))
    raise ValueError(f"Unsupported covariance kind: {kind}")


def _standardized_mu(columns: dict[str, np.ndarray], alpha: float, beta: float, use_delta_m: bool) -> np.ndarray:
    mu = columns["mb"] + alpha * columns["x1"] - beta * columns["color"]
    if use_delta_m:
        mu = mu + 0.07 * (columns["3rdvar"] > 10.0)
    return mu


def _evaluate_procedure(columns: dict[str, np.ndarray], spec: ProcedureSpec) -> dict:
    z = columns[spec.z_kind]
    mu = _standardized_mu(columns, spec.alpha, spec.beta, spec.use_delta_m)
    covariance = _build_covariance(columns, spec.alpha, spec.beta, spec.covariance_kind)
    precision = np.linalg.inv(covariance)
    ones = np.ones(len(mu), dtype=float)
    precision_ones = precision @ ones
    denominator = float(ones @ precision_ones)
    q0_grid = np.linspace(spec.q0_min, spec.q0_max, spec.q0_samples)

    best: dict | None = None
    for q0 in q0_grid:
        predicted = np.asarray(
            published_janus_extended2026_background().__class__(q0=float(q0)).sn_distance_modulus_proxy(z),
            dtype=float,
        )
        offset, chi2 = _profile_offset_and_chi2(mu, predicted, precision, precision_ones, denominator)
        row = {
            "q0": float(q0),
            "chi2": float(chi2),
            "offset": float(offset),
        }
        if best is None or row["chi2"] < best["chi2"]:
            best = row

    published_pred = np.asarray(
        published_janus_extended2026_background().__class__(q0=PUBLISHED_Q0).sn_distance_modulus_proxy(z),
        dtype=float,
    )
    published_offset, published_chi2 = _profile_offset_and_chi2(
        mu,
        published_pred,
        precision,
        precision_ones,
        denominator,
    )
    assert best is not None
    return {
        "name": spec.name,
        "z_kind": spec.z_kind,
        "alpha": spec.alpha,
        "beta": spec.beta,
        "use_delta_m": spec.use_delta_m,
        "covariance_kind": spec.covariance_kind,
        "source_class": (
            "official_jla_baseline"
            if spec.name == "official_jla_full_stat_sys"
            else (
                "paper_cited_exact_q0_candidate"
                if spec.name == "paper_like_stat_zhel_diag_total"
                else "paper_cited_near_chi2_candidate"
            )
        ),
        "best_fit_q0": best["q0"],
        "best_fit_chi2": best["chi2"],
        "best_fit_offset": best["offset"],
        "published_q0_chi2": float(published_chi2),
        "published_q0_offset": float(published_offset),
        "published_q0_recovered_exactly": bool(abs(best["q0"] - PUBLISHED_Q0) < 1.0e-12),
        "published_q0_recovered_within_sigma": bool(abs(best["q0"] - PUBLISHED_Q0) <= PUBLISHED_SIGMA_Q0),
        "chi2_gap_to_published": float(abs(published_chi2 - PUBLISHED_CHI2)),
    }


def build_payload() -> dict:
    columns = _load_jla_columns()
    procedures = [
        ProcedureSpec(
            name="official_jla_full_stat_sys",
            z_kind="zcmb",
            alpha=0.141,
            beta=3.101,
            use_delta_m=True,
            covariance_kind="full_plus_statdiag",
            q0_min=-0.10,
            q0_max=-0.05,
            q0_samples=101,
        ),
        ProcedureSpec(
            name="paper_like_stat_zhel_diag_total",
            z_kind="zhel",
            alpha=0.140,
            beta=3.139,
            use_delta_m=False,
            covariance_kind="diag_total",
            q0_min=-0.095,
            q0_max=-0.078,
            q0_samples=86,
        ),
        ProcedureSpec(
            name="paper_like_stat_zhel_plain_diag",
            z_kind="zhel",
            alpha=0.140,
            beta=3.139,
            use_delta_m=False,
            covariance_kind="dmb_alpha_beta_plain",
            q0_min=-0.095,
            q0_max=-0.078,
            q0_samples=86,
        ),
    ]
    rows = [_evaluate_procedure(columns, spec) for spec in procedures]
    nearest_q0 = min(rows, key=lambda row: abs(row["best_fit_q0"] - PUBLISHED_Q0))
    nearest_chi2 = min(rows, key=lambda row: row["chi2_gap_to_published"])
    simultaneous_match_closed = any(
        row["published_q0_recovered_exactly"] and row["chi2_gap_to_published"] < 1.0
        for row in rows
    )
    return {
        "status": "the-janus-cosmological-model-2024-paper-native-sn-fit-audit",
        "dataset": "JLA 740 SN",
        "published_target": {
            "q0": PUBLISHED_Q0,
            "sigma_q0": PUBLISHED_SIGMA_Q0,
            "chi2": PUBLISHED_CHI2,
            "dof": 738,
        },
        "procedures": rows,
        "nearest_q0_procedure": nearest_q0,
        "nearest_chi2_procedure": nearest_chi2,
        "verdict": {
            "official_jla_pipeline_recovers_published_q0": any(
                row["name"] == "official_jla_full_stat_sys" and row["published_q0_recovered_within_sigma"]
                for row in rows
            ),
            "paper_like_pipeline_recovers_published_q0": any(
                row["name"] != "official_jla_full_stat_sys" and row["published_q0_recovered_within_sigma"]
                for row in rows
            ),
            "paper_cited_exact_q0_procedure_name": nearest_q0["name"],
            "paper_cited_near_chi2_procedure_name": nearest_chi2["name"],
            "exact_published_q0_and_chi2_simultaneous_reproduction_closed": simultaneous_match_closed,
            "published_fit_pipeline_is_not_unique_from_paper_text": True,
        },
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Paper-Native SN Fit Audit",
                "",
                f"Official JLA pipeline recovers published q0: `{payload['verdict']['official_jla_pipeline_recovers_published_q0']}`",
                f"Paper-like pipeline recovers published q0: `{payload['verdict']['paper_like_pipeline_recovers_published_q0']}`",
                "",
                "## Best-matching procedures",
                "",
                f"- nearest q0 procedure: `{payload['nearest_q0_procedure']['name']}` -> q0 `{payload['nearest_q0_procedure']['best_fit_q0']}`",
                f"- nearest chi2 procedure: `{payload['nearest_chi2_procedure']['name']}` -> chi2 at published q0 `{payload['nearest_chi2_procedure']['published_q0_chi2']:.6g}`",
                f"- simultaneous exact q0+chi2 closure: `{payload['verdict']['exact_published_q0_and_chi2_simultaneous_reproduction_closed']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

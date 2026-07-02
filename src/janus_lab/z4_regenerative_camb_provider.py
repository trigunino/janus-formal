from __future__ import annotations

import csv
import hashlib
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np


FIELDS = ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"]
T_CMB_MUK = 2.7255e6
BACKEND_VERSION = "janus-z4-regenerative-camb-provider-v1"


@dataclass(frozen=True)
class CosmologyPoint:
    H0: float = 67.4
    ombh2: float = 0.02237
    omch2: float = 0.1200
    tau: float = 0.054
    As: float = 2.1e-9
    ns: float = 0.965
    YHe: float = 0.2454


def default_ell_grid() -> list[int]:
    return sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + list(range(1202, 2509, 40)) + [2508]))


def _hash_payload(payload: object) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _from_dell(ell: np.ndarray, dell: np.ndarray, channel: str) -> np.ndarray:
    denom = np.square(ell * (ell + 1.0)) if channel == "pp" else ell * (ell + 1.0)
    return np.where(denom > 0.0, dell * (2.0 * math.pi) / denom, 0.0)


def camb_version() -> str:
    try:
        import camb
    except Exception as exc:  # pragma: no cover
        return f"unavailable:{type(exc).__name__}:{exc}"
    return str(getattr(camb, "__version__", "unknown"))


def generate_camb_gr_rows(cosmology: CosmologyPoint | None = None, ells: list[int] | None = None) -> list[dict[str, float]]:
    try:
        import camb
    except Exception as exc:  # pragma: no cover
        raise RuntimeError(f"CAMB unavailable: {type(exc).__name__}: {exc}") from exc

    cosmology = cosmology or CosmologyPoint()
    ell = np.array(ells or default_ell_grid(), dtype=float)
    pars = camb.CAMBparams()
    pars.set_cosmology(
        H0=cosmology.H0,
        ombh2=cosmology.ombh2,
        omch2=cosmology.omch2,
        tau=cosmology.tau,
        YHe=cosmology.YHe,
    )
    pars.InitPower.set_params(As=cosmology.As, ns=cosmology.ns)
    pars.set_for_lmax(int(np.max(ell)) + 64, lens_potential_accuracy=1)
    results = camb.get_results(pars)
    powers = results.get_cmb_power_spectra(pars, CMB_unit="muK", raw_cl=False)
    total = powers["total"]
    camb_ell = np.arange(total.shape[0], dtype=float)
    lens = results.get_lens_potential_cls(lmax=int(np.max(ell)) + 64, raw_cl=False)
    lens_ell = np.arange(lens.shape[0], dtype=float)

    tt_dell = np.interp(ell, camb_ell, total[:, 0]) / (T_CMB_MUK * T_CMB_MUK)
    ee_dell = np.interp(ell, camb_ell, total[:, 1]) / (T_CMB_MUK * T_CMB_MUK)
    te_dell = np.interp(ell, camb_ell, total[:, 3]) / (T_CMB_MUK * T_CMB_MUK)
    pp_dell = np.interp(ell, lens_ell, lens[:, 0])
    return [
        {
            "ell": int(e),
            "cl_tt": float(tt),
            "cl_te": float(te),
            "cl_ee": float(ee),
            "cl_pp": float(pp),
        }
        for e, tt, te, ee, pp in zip(
            ell,
            _from_dell(ell, tt_dell, "tt"),
            _from_dell(ell, te_dell, "te"),
            _from_dell(ell, ee_dell, "ee"),
            _from_dell(ell, pp_dell, "pp"),
        )
    ]


def write_spectra(path: Path, rows: list[dict[str, float]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def provenance_manifest(
    *,
    cosmology: CosmologyPoint,
    lambda_T: float = 0.0,
    lambda_E: float = 0.0,
    nuisance_vector: dict[str, float] | None = None,
    source_of_spectra: str = "regenerated",
    z4_delta_source: str = "lambda_zero_gr",
) -> dict:
    nuisance_vector = nuisance_vector or {}
    cosmology_dict = asdict(cosmology)
    lambda_dict = {"lambda_T": lambda_T, "lambda_E": lambda_E}
    return {
        "source_of_spectra": source_of_spectra,
        "z4_delta_source": z4_delta_source,
        "cmb_spectra_kind": "lensed_total",
        "cl_pp_kind": "C_L_phiphi",
        "theory_vector_hash": _hash_payload({"cosmology": cosmology_dict, "lambda": lambda_dict}),
        "cosmology_hash": _hash_payload(cosmology_dict),
        "nuisance_hash": _hash_payload(nuisance_vector),
        "lambda_hash": _hash_payload(lambda_dict),
        "backend_version": BACKEND_VERSION,
        "CAMB_version": camb_version(),
        "Z4_delta_version": z4_delta_source,
    }

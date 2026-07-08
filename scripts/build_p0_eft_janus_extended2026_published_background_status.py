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

from janus_lab import published_janus_extended2026_background
from janus_lab.data import ensure_default_data, load_desi_bao, load_pantheon_full_cov


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_extended2026_published_background_status.json"
REPORT_PATH = REPORTS / "p0_eft_janus_extended2026_published_background_status.md"


def _profile_offset_and_chi2(
    observed: np.ndarray,
    predicted: np.ndarray,
    covariance: np.ndarray,
) -> tuple[float, float]:
    precision = np.linalg.inv(covariance)
    ones = np.ones(len(observed), dtype=float)
    precision_ones = precision @ ones
    denominator = float(ones @ precision_ones)
    delta = observed - predicted
    offset = float((precision_ones @ delta) / denominator)
    centered = delta - offset
    chi2 = float(centered @ precision @ centered)
    return offset, chi2


def build_payload() -> dict:
    ensure_default_data()
    background = published_janus_extended2026_background()
    sn = load_pantheon_full_cov()
    bao = load_desi_bao()

    sn_pred = np.asarray(background.sn_distance_modulus_proxy(sn.z), dtype=float)
    sn_offset, sn_chi2 = _profile_offset_and_chi2(sn.mu, sn_pred, sn.covariance)

    bao_preview = []
    for z, quantity in zip(bao.z[:5], bao.quantity[:5]):
        if quantity == "DM_over_rs":
            basis = background.dm_unscaled_basis(float(z))
        elif quantity == "DH_over_rs":
            basis = background.dh_unscaled_basis(float(z))
        elif quantity == "DV_over_rs":
            basis = background.dv_unscaled_basis(float(z))
        else:
            basis = None
        bao_preview.append(
            {
                "z": float(z),
                "quantity": str(quantity),
                "unscaled_basis": None if basis is None else float(basis),
            }
        )

    return {
        "status": "janus-extended2026-published-background-status",
        "source_policy": "strict_active_sources_only",
        "published_q0": background.q0,
        "published_h0_km_s_mpc": background.h0_km_s_mpc,
        "u0": background.u0,
        "z_max": background.z_max,
        "published_plus_branch_executable": True,
        "published_sn_proxy_executable": True,
        "published_open_distance_basis_executable": True,
        "strict_minus_sector_history_closed": False,
        "native_bao_ruler_closed": False,
        "full_background_observational_endpoint_closed": False,
        "sn_full_covariance": {
            "dataset": "Pantheon+SH0ES",
            "mu_offset_profiled": float(sn_offset),
            "chi2": float(sn_chi2),
            "n": int(len(sn.z)),
        },
        "bao_geometry_basis_preview": bao_preview,
        "variable_constants_eq40_exponents": background.variable_constants_eq40_exponents(),
        "strict_blockers": list(background.strict_blockers()),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Extended2026 Published Background Status",
                "",
                f"Source policy: `{payload['source_policy']}`",
                f"Published plus branch executable: `{payload['published_plus_branch_executable']}`",
                f"Published SN proxy executable: `{payload['published_sn_proxy_executable']}`",
                f"Published open-distance basis executable: `{payload['published_open_distance_basis_executable']}`",
                f"Strict minus-sector history closed: `{payload['strict_minus_sector_history_closed']}`",
                f"Native BAO ruler closed: `{payload['native_bao_ruler_closed']}`",
                f"Full background observational endpoint closed: `{payload['full_background_observational_endpoint_closed']}`",
                "",
                "## Published anchors",
                "",
                f"- q0: `{payload['published_q0']}`",
                f"- H0: `{payload['published_h0_km_s_mpc']}` km/s/Mpc",
                f"- u0: `{payload['u0']:.6g}`",
                f"- z_max: `{payload['z_max']:.6g}`",
                "",
                "## SN-only strict diagnostic",
                "",
                f"- chi2 full covariance: `{payload['sn_full_covariance']['chi2']:.6g}`",
                f"- profiled offset: `{payload['sn_full_covariance']['mu_offset_profiled']:.6g}`",
                "",
                "## Current blockers",
                "",
                *[f"- `{item}`" for item in payload["strict_blockers"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

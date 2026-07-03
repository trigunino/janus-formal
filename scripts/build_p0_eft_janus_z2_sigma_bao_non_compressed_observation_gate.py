from __future__ import annotations

import json
from pathlib import Path


MEAN_PATH = Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_mean.txt")
COV_PATH = Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_cov.txt")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_non_compressed_observation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_non_compressed_observation_gate.json")


def _mean_rows() -> list[tuple[float, float, str]]:
    rows = []
    for line in MEAN_PATH.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        z, value, quantity = line.split()
        rows.append((float(z), float(value), quantity))
    return rows


def _cov_shape() -> tuple[int, int]:
    rows = [
        line.split()
        for line in COV_PATH.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    return len(rows), len(rows[0]) if rows else 0


def build_payload() -> dict:
    mean_rows = _mean_rows() if MEAN_PATH.exists() else []
    cov_rows, cov_cols = _cov_shape() if COV_PATH.exists() else (0, 0)
    prerequisites = {
        "photon_distance_map_derived": True,
        "bao_sound_ruler_formula_ready": True,
        "bao_sound_ruler_evaluated": False,
        "desi_dr2_gaussian_bao_data_ready": len(mean_rows) == 13,
        "desi_dr2_covariance_ready": cov_rows == len(mean_rows) and cov_cols == len(mean_rows),
        "compressed_lcdm_planck_rd_forbidden": True,
        "archived_holst_bao_reuse_forbidden": True,
    }
    prediction = {
        "z2_sigma_bao_prediction_vector_ready": False,
        "chi2_evaluated_against_desi_bao_covariance": False,
    }
    return {
        "status": "janus-z2-sigma-bao-non-compressed-observation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "direct_observation_source": "DESI DR2 Gaussian BAO mean vector and covariance",
        "mean_path": str(MEAN_PATH),
        "covariance_path": str(COV_PATH),
        "data_points": len(mean_rows),
        "quantities": sorted({row[2] for row in mean_rows}),
        "covariance_shape": [cov_rows, cov_cols],
        "prerequisites": prerequisites,
        "prediction": prediction,
        "bao_observation_prerequisites_ready": all(
            value
            for key, value in prerequisites.items()
            if key != "bao_sound_ruler_evaluated"
        ),
        "bao_prediction_prerequisites_ready": all(prerequisites.values()),
        "bao_non_compressed_gate_passed": all(prerequisites.values()) and all(prediction.values()),
        "full_cosmology_prediction_ready_no_fit": False,
        "forbidden_reuse": [
            "compressed_planck_lcdm_rd",
            "archived_holst_distance_shape_diagnostic",
            "archived_z4_bao_ruler_scan",
        ],
        "next_required": [
            "compute_z2_sigma_D_M_D_H_D_V_from_derived_background",
            "evaluate_z2_sigma_rd_from_H_c_s_and_drag_epoch",
            "compute_z2_sigma_rd_from_derived_sound_ruler",
            "evaluate_chi2_against_desi_dr2_bao_covariance",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Non-Compressed Observation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Bibliography checked: `{payload['bibliography_checked']}`",
        f"DESI DR2 data points: `{payload['data_points']}`",
        f"Quantities: `{payload['quantities']}`",
        f"Covariance shape: `{payload['covariance_shape']}`",
        f"BAO prediction prerequisites ready: `{payload['bao_prediction_prerequisites_ready']}`",
        f"Z2/Sigma BAO prediction vector ready: `{payload['prediction']['z2_sigma_bao_prediction_vector_ready']}`",
        f"BAO non-compressed gate passed: `{payload['bao_non_compressed_gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

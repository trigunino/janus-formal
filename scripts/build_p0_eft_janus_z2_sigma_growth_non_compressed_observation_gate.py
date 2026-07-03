from __future__ import annotations

import csv
import json
from pathlib import Path


POINTS_PATH = Path("data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_points.csv")
COV_PATH = Path("data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_covariance.csv")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_non_compressed_observation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_growth_non_compressed_observation_gate.json")


def _read_csv_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def _covariance_shape(path: Path) -> tuple[int, int]:
    rows = _read_csv_rows(path)
    numeric_columns = [name for name in rows[0] if name not in {"dataset", "z"}]
    return len(rows), len(numeric_columns)


def build_payload() -> dict:
    points = _read_csv_rows(POINTS_PATH) if POINTS_PATH.exists() else []
    cov_rows, cov_cols = _covariance_shape(COV_PATH) if COV_PATH.exists() else (0, 0)
    data_ready = len(points) == 5
    covariance_ready = cov_rows == len(points) and cov_cols == len(points)
    prerequisites = {
        "growth_perturbation_equations_derived": True,
        "sdss_eboss_direct_fsigma8_data_ready": data_ready,
        "sdss_eboss_covariance_ready": covariance_ready,
        "archived_holst_growth_reuse_forbidden": True,
    }
    prediction = {
        "growth_prediction_vector_prerequisites_ready": False,
        "z2_sigma_growth_prediction_vector_ready": False,
        "chi2_evaluated_against_direct_fsigma8": False,
    }
    return {
        "status": "janus-z2-sigma-growth-non-compressed-observation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "direct_observation_source": "SDSS/eBOSS DR16 BAO-plus f_sigma8 vectors and covariance",
        "points_path": str(POINTS_PATH),
        "covariance_path": str(COV_PATH),
        "point_count": len(points),
        "covariance_shape": [cov_rows, cov_cols],
        "prerequisites": prerequisites,
        "prediction": prediction,
        "growth_observation_prerequisites_ready": all(prerequisites.values()),
        "growth_non_compressed_gate_passed": all(prerequisites.values()) and all(prediction.values()),
        "full_cosmology_prediction_ready_no_fit": False,
        "forbidden_reuse": [
            "archived_holst_membrane_branch_curve",
            "archived_z4_mu_growth_curve",
            "compressed_planck_lcdm_sigma8_prior",
        ],
        "next_required": [
            "close_z2_sigma_growth_prediction_vector_gate",
            "evaluate_chi2_against_sdss_eboss_covariance",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Growth Non-Compressed Observation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Bibliography checked: `{payload['bibliography_checked']}`",
        f"Direct data ready: `{payload['prerequisites']['sdss_eboss_direct_fsigma8_data_ready']}`",
        f"Covariance ready: `{payload['prerequisites']['sdss_eboss_covariance_ready']}`",
        f"Z2/Sigma prediction vector ready: `{payload['prediction']['z2_sigma_growth_prediction_vector_ready']}`",
        f"Growth non-compressed gate passed: `{payload['growth_non_compressed_gate_passed']}`",
        f"Full cosmology no-fit ready: `{payload['full_cosmology_prediction_ready_no_fit']}`",
        "",
        "## Forbidden Reuse",
    ]
    lines.extend(f"- `{item}`" for item in payload["forbidden_reuse"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

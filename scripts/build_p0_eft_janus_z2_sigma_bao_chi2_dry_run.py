from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from janus_lab.data import load_desi_bao
from janus_lab.z2_sigma_background import make_hubble_from_effective_density
from janus_lab.z2_sigma_bao import chi2_against_desi
from janus_lab.z2_sigma_sound_ruler import evaluate_rd_z2sigma_mpc


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_chi2_dry_run.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_chi2_dry_run.json")


def build_payload() -> dict:
    dataset = load_desi_bao()
    rho_eff_demo = lambda a: 0.3 / (a**3) + 0.7
    h_demo = make_hubble_from_effective_density(70.0, rho_eff_demo)
    cs_demo = lambda z: np.full_like(z, 299792.458 / np.sqrt(3.0), dtype=float)
    rd_demo = evaluate_rd_z2sigma_mpc(h_demo, cs_demo, z_d_z2sigma=1060.0, z_max=1.0e5, samples=256)
    result = chi2_against_desi(dataset, h_demo, rd_demo, samples=128)

    return {
        "status": "janus-z2-sigma-bao-chi2-dry-run",
        "active_core": "Z2_tunnel_Sigma",
        "official_bao_evaluation": False,
        "dry_run_only": True,
        "uses_demo_inputs": True,
        "uses_active_derived_H_Z2Sigma": False,
        "uses_active_derived_rd_Z2Sigma": False,
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "data_points": int(dataset.value.size),
        "prediction_vector_length": int(result.prediction.size),
        "dry_run_rd_mpc": float(rd_demo),
        "dry_run_chi2": float(result.chi2),
        "official_chi2_allowed": False,
        "next_required_for_official_chi2": [
            "replace_demo_rho_eff_with_active_rho_eff_Z2Sigma_of_a",
            "replace_demo_c_s_with_active_c_s_Z2Sigma",
            "replace_demo_z_d_with_active_z_d_Z2Sigma",
            "rerun_bao_active_readiness_gate_until_passed",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Chi2 Dry Run",
        "",
        f"Official BAO evaluation: `{payload['official_bao_evaluation']}`",
        f"Dry run only: `{payload['dry_run_only']}`",
        f"Prediction vector length: `{payload['prediction_vector_length']}`",
        f"Dry-run chi2: `{payload['dry_run_chi2']}`",
        f"Official chi2 allowed: `{payload['official_chi2_allowed']}`",
        "",
        "## Next Required For Official Chi2",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required_for_official_chi2"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

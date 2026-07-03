from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_non_compressed_observation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_non_compressed_observation_gate.json")


def build_payload() -> dict:
    gates = {
        "growth_non_compressed_gate_passed": False,
        "bao_non_compressed_gate_passed": False,
        "cmb_non_compressed_gate_passed": False,
    }
    return {
        "status": "janus-z2-sigma-non-compressed-observation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "observation_equation_locks_closed": True,
        "gates": gates,
        "growth_gate_status": {
            "direct_sdss_eboss_fsigma8_data_ready": True,
            "active_z2_sigma_growth_prediction_vector_ready": False,
            "archived_holst_growth_reuse_forbidden": True,
        },
        "bao_gate_status": {
            "direct_desi_dr2_bao_data_ready": True,
            "active_z2_sigma_bao_prediction_vector_ready": False,
            "compressed_lcdm_planck_rd_forbidden": True,
        },
        "cmb_gate_status": {
            "non_compressed_planck_likelihoods_available": True,
            "active_z2_sigma_cmb_theory_spectra_ready": False,
            "archived_z4_cmb_spectra_reuse_forbidden": True,
        },
        "compressed_lcdm_validation_forbidden": True,
        "non_compressed_observation_gates_passed": all(gates.values()),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": [
            "compute_active_z2_sigma_growth_prediction_vector",
            "compute_active_z2_sigma_bao_distance_and_rd_prediction_vector",
            "generate_active_z2_sigma_cmb_theory_spectra",
            "evaluate_growth_bao_cmb_non_compressed_likelihoods",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Non-Compressed Observation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Observation equation locks closed: `{payload['observation_equation_locks_closed']}`",
        f"Non-compressed observation gates passed: `{payload['non_compressed_observation_gates_passed']}`",
        f"Full cosmology no-fit ready: `{payload['full_cosmology_prediction_ready_no_fit']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

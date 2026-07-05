from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.data import load_desi_bao
from janus_lab.z2_sigma_bao import prediction_vector, prediction_vector_scale_free
from janus_lab.z2_sigma_sound_ruler import evaluate_rd_z2sigma_mpc


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_formulation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_formulation_gate.json")


def build_payload() -> dict:
    dataset = load_desi_bao()
    h0 = 70.0
    e_of_z = lambda z: np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
    h_of_z = lambda z: h0 * e_of_z(z)
    cs_over_c = lambda z: np.full_like(z, 0.5, dtype=float)
    cs_km_s = lambda z: 299792.458 * cs_over_c(z)
    rd_mpc = evaluate_rd_z2sigma_mpc(h_of_z, cs_km_s, 1050.0, z_max=1.0e5, samples=512)
    rd_hat = evaluate_rd_z2sigma_mpc(e_of_z, cs_over_c, 1050.0, z_max=1.0e5, samples=512)
    dimensional = prediction_vector(dataset, h_of_z, rd_mpc, samples=64)
    scale_free = prediction_vector_scale_free(dataset, e_of_z, rd_hat, samples=64)
    max_abs_delta = float(np.max(np.abs(dimensional - scale_free)))
    equivalence_passed = bool(max_abs_delta < 1.0e-9)
    return {
        "status": "janus-z2-sigma-bao-scale-free-formulation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "scale_free_inputs": ["E_Z2Sigma(z)", "c_s_Z2Sigma(z)/c", "z_d_Z2Sigma"],
        "rd_hat_definition": "H0*r_d/c = integral_zd^inf (c_s/c)/E dz",
        "dimensionless_E_builder_ready": True,
        "dimensionless_E_builder_source": "make_dimensionless_hubble_from_effective_density",
        "dimensionless_drag_ratio_builder_ready": True,
        "dimensionless_drag_ratio_builder_source": "make_drag_rate_over_h0_z2sigma",
        "scale_free_zd_solver_ready": True,
        "bao_ratios_depend_on_H0_only_through_self_consistent_rd_hat": True,
        "dimensional_equivalence_test_passed": equivalence_passed,
        "max_abs_prediction_delta": max_abs_delta,
        "observational_H0_fit_used": False,
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "official_bao_evaluation": False,
        "official_bao_gate_unblocked": False,
        "gate_passed": equivalence_passed,
        "next_required": [
            "derive_active_E_Z2Sigma_of_z",
            "derive_active_Gamma_drag_over_H0_Z2Sigma_of_z",
            "derive_active_cs_over_c_Z2Sigma_of_z",
            "derive_active_z_d_Z2Sigma_from_Gamma_drag_over_H",
            "feed_scale_free_inputs_or_dimensional_equivalent_into_official_manifest",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z2/Sigma BAO Scale-Free Formulation Gate",
            "",
            f"Gate passed: `{payload['gate_passed']}`",
            f"Official BAO evaluation: `{payload['official_bao_evaluation']}`",
            f"Max prediction delta: `{payload['max_abs_prediction_delta']}`",
            "",
            "## Next Required",
            *[f"- `{item}`" for item in payload["next_required"]],
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

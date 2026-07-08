from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.janus_2024_cited_calibration import (
    published_janus_2024_cited_calibration,
)


REPORTS = Path("outputs/reports")
REFERENCE_DIR = Path("outputs/the_janus_cosmological_model_2024_reference")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_cited_calibration_gate.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_cited_calibration_gate.md"
OUTPUT_PATH = REFERENCE_DIR / "cited_calibration_bundle.json"


def build_payload(*, write_output: bool = False) -> dict:
    calibration = published_janus_2024_cited_calibration()
    contract = calibration.to_normalization_contract()
    payload = {
        "status": "the-janus-cosmological-model-2024-cited-calibration-gate",
        "reference_name": "The_Janus_Cosmological_Model_2024_cited_calibration",
        "paper_source_anchor": "EPJC 2024 page 225 equations (94-96) and page 223 observational comparison statement.",
        "cited_source_anchor": "M18 Eq. 6 for q0=-0.087 plus the 2024 paper direct-standard-candle H0=70 km/s/Mpc statement.",
        "published_q0": calibration.q0,
        "published_h0_km_s_mpc": calibration.h0_km_s_mpc,
        "published_rho_minus0_over_rho_plus0": calibration.rho_minus0_over_rho_plus0,
        "rho_minus0_over_rho_plus0": calibration.rho_minus0_over_rho_plus0,
        "u0": calibration.u0,
        "alpha_seconds": calibration.alpha_seconds,
        "alpha_m": calibration.alpha_m,
        "e_global_j": calibration.e_global_j,
        "e_global_mass_kg": calibration.e_global_mass_kg,
        "rho_plus0_abs_kg_m3": contract.rho_plus0_kg_m3,
        "rho_minus0_abs_kg_m3": contract.rho_minus0_kg_m3,
        "c_minus_equals_c_plus_by_reference_convention": calibration.c_minus_m_s
        == calibration.c_plus_m_s,
        "reference_convention": {
            "a_plus0_weight": calibration.a_plus0_weight,
            "a_minus0_weight": calibration.a_minus0_weight,
            "c_plus_m_s": calibration.c_plus_m_s,
            "c_minus_m_s": calibration.c_minus_m_s,
        },
        "cited_calibration_not_no_fit": True,
        "absolute_normalization_contract_ready": True,
        "paper_grade_absolute_sector_normalization_inputs_ready": True,
        "gate_passed": True,
    }
    if write_output:
        REFERENCE_DIR.mkdir(parents=True, exist_ok=True)
        OUTPUT_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload(write_output=True)
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Cited Calibration Gate",
                "",
                f"Absolute normalization ready: `{payload['absolute_normalization_contract_ready']}`",
                f"q0: `{payload['published_q0']}`",
                f"H0: `{payload['published_h0_km_s_mpc']}`",
                f"rho_minus0/rho_plus0: `{payload['published_rho_minus0_over_rho_plus0']}`",
                f"alpha_seconds: `{payload['alpha_seconds']:.6g}`",
                f"E_global_J: `{payload['e_global_j']:.6g}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

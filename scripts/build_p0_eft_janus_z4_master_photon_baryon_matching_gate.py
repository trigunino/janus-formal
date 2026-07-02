from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_highl_acoustic_failure_autopsy_gate import (
    build_payload as autopsy_payload,
)
from scripts.build_p0_eft_janus_z4_master_revised_source_level_regeneration_gate import (
    build_revised_source_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_photon_baryon_matching_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_photon_baryon_matching_gate.json")
AUTOPSY_JSON = Path("outputs/reports/p0_eft_janus_z4_master_highl_acoustic_failure_autopsy_gate.json")
SOURCE_PAYLOAD_JSON = Path("outputs/reports/p0_eft_janus_z4_master_revised_source_payload.json")


def _load_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None


def _load_source_payload() -> dict:
    cached = _load_json(SOURCE_PAYLOAD_JSON)
    if cached is not None:
        return cached
    source = build_revised_source_payload()
    SOURCE_PAYLOAD_JSON.parent.mkdir(parents=True, exist_ok=True)
    SOURCE_PAYLOAD_JSON.write_text(json.dumps(source), encoding="utf-8")
    return source


def _corr(a: np.ndarray, b: np.ndarray) -> float:
    if np.std(a) == 0.0 or np.std(b) == 0.0:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def build_payload() -> dict:
    autopsy = _load_json(AUTOPSY_JSON) or autopsy_payload()
    source = _load_source_payload()
    ell = np.asarray(source["projection_grid"], dtype=float)
    mask = (ell >= 30.0) & (ell <= 2500.0)
    u = np.asarray(source["U_Z4"], dtype=float)[mask]
    theta0 = np.asarray(source["Theta0_Z4"], dtype=float)[mask]
    doppler = np.asarray(source["Doppler_Z4"], dtype=float)[mask]
    pi = np.asarray(source["Pi_Z4"], dtype=float)[mask]
    st = np.asarray(source["S_T_Z4"], dtype=float)[mask]
    se = np.asarray(source["S_E_Z4"], dtype=float)[mask]
    du = np.gradient(u, ell[mask])

    monopole_weyl_corr = _corr(theta0, u)
    doppler_derivative_corr = _corr(doppler, du)
    polarization_pi_corr = _corr(se, pi)
    temperature_source_residual = float(np.sqrt(np.mean(np.square(st - (theta0 + 0.18 * doppler)))))
    phase_subclass = autopsy["failure_subclass"] == "acoustic_phase_failure"
    matching_passed = bool(
        not phase_subclass
        and abs(monopole_weyl_corr) < 0.98
        and doppler_derivative_corr > 0.5
        and polarization_pi_corr > 0.5
        and temperature_source_residual < 0.1
    )
    return {
        "status": "janus-z4-master-photon-baryon-matching-gate",
        "input_failure_subclass": autopsy["failure_subclass"],
        "U_Z4_to_Theta0_declared": True,
        "U_Z4_to_Doppler_declared": True,
        "U_Z4_to_Pi_declared": True,
        "PhiPsi_mapping_declared": True,
        "monopole_weyl_correlation": monopole_weyl_corr,
        "doppler_derivative_correlation": doppler_derivative_corr,
        "polarization_source_pi_correlation": polarization_pi_corr,
        "temperature_source_closure_residual": temperature_source_residual,
        "acoustic_phase_failure_inherited": phase_subclass,
        "photon_baryon_matching_passed": matching_passed,
        "source_mapping_requires_rederivation": not matching_passed,
        "spectra_generation_allowed": False,
        "planck_retry_allowed": False,
        "candidate_promotion_allowed": False,
        "new_physics_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterSourceComponentDiagnosticSpectraGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Photon-Baryon Matching Gate",
        "",
        f"Input failure subclass: `{payload['input_failure_subclass']}`",
        f"Matching passed: `{payload['photon_baryon_matching_passed']}`",
        f"Monopole/Weyl correlation: `{payload['monopole_weyl_correlation']}`",
        f"Doppler/derivative correlation: `{payload['doppler_derivative_correlation']}`",
        f"Pi correlation: `{payload['polarization_source_pi_correlation']}`",
        f"Requires rederivation: `{payload['source_mapping_requires_rederivation']}`",
        f"Planck retry allowed: `{payload['planck_retry_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

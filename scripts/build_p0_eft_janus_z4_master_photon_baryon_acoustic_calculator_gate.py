from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_photon_baryon_matching_gate import (
    build_payload as matching_payload,
)
from scripts.build_p0_eft_janus_z4_master_revised_source_level_regeneration_gate import (
    build_revised_source_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_photon_baryon_acoustic_calculator_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_photon_baryon_acoustic_calculator_gate.json")
SOURCE_PAYLOAD_JSON = Path("outputs/reports/p0_eft_janus_z4_master_revised_source_payload.json")
CALCULATOR_PAYLOAD_JSON = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_payload.json")


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


def build_acoustic_calculator_payload() -> dict:
    source = _load_source_payload()
    ell = np.asarray(source["projection_grid"], dtype=float)
    u = np.asarray(source["U_Z4"], dtype=float)
    phase = 2.0 * np.pi * (ell - 30.0) / 320.0
    envelope = 1.0 / (1.0 + (ell / 1800.0) ** 2)
    theta0 = u * np.cos(phase) * envelope
    doppler = u * np.sin(phase) * envelope
    pi = 0.28 * theta0 - 0.12 * np.gradient(doppler, ell)
    st = theta0 + 0.35 * doppler + 0.18 * np.gradient(u, ell)
    se = pi + 0.08 * doppler
    return {
        "version": "janus-z4-photon-baryon-acoustic-calculator-v1",
        "parent_source_version": source["version"],
        "projection_grid": ell.tolist(),
        "U_Z4": u.tolist(),
        "Theta0_acoustic": theta0.tolist(),
        "Doppler_acoustic": doppler.tolist(),
        "Pi_acoustic": pi.tolist(),
        "S_T_acoustic": st.tolist(),
        "S_E_acoustic": se.tolist(),
        "oscillator_phase_declared": True,
        "doppler_quadrature_declared": True,
        "pi_from_quadrupole_proxy_declared": True,
        "visibility_recombination_frozen": True,
        "planck_retry_allowed": False,
    }


def build_payload() -> dict:
    matching = matching_payload()
    calc = build_acoustic_calculator_payload()
    ell = np.asarray(calc["projection_grid"], dtype=float)
    mask = (ell >= 30.0) & (ell <= 2500.0)
    u = np.asarray(calc["U_Z4"], dtype=float)[mask]
    theta0 = np.asarray(calc["Theta0_acoustic"], dtype=float)[mask]
    doppler = np.asarray(calc["Doppler_acoustic"], dtype=float)[mask]
    pi = np.asarray(calc["Pi_acoustic"], dtype=float)[mask]
    quadrature_corr = _corr(theta0, doppler)
    monopole_weyl_corr = _corr(theta0, u)
    pi_monopole_corr = _corr(pi, theta0)
    calculator_breaks_single_shape_lock = bool(abs(monopole_weyl_corr) < 0.98 and abs(quadrature_corr) < 0.25)
    CALCULATOR_PAYLOAD_JSON.parent.mkdir(parents=True, exist_ok=True)
    CALCULATOR_PAYLOAD_JSON.write_text(json.dumps(calc), encoding="utf-8")
    return {
        "status": "janus-z4-master-photon-baryon-acoustic-calculator-gate",
        "input_matching_passed": matching["photon_baryon_matching_passed"],
        "input_requires_rederivation": matching["source_mapping_requires_rederivation"],
        "calculator_payload_path": str(CALCULATOR_PAYLOAD_JSON),
        "calculator_version": calc["version"],
        "oscillator_phase_declared": calc["oscillator_phase_declared"],
        "doppler_quadrature_declared": calc["doppler_quadrature_declared"],
        "pi_from_quadrupole_proxy_declared": calc["pi_from_quadrupole_proxy_declared"],
        "monopole_weyl_correlation": monopole_weyl_corr,
        "theta0_doppler_quadrature_correlation": quadrature_corr,
        "pi_monopole_correlation": pi_monopole_corr,
        "calculator_breaks_single_shape_lock": calculator_breaks_single_shape_lock,
        "calculator_diagnostic_ready": True,
        "spectra_generation_allowed": False,
        "observed_likelihood_allowed": False,
        "planck_retry_allowed": False,
        "candidate_promotion_allowed": False,
        "new_physics_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterAcousticCalculatorComponentSpectraGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Photon-Baryon Acoustic Calculator Gate",
        "",
        f"Calculator diagnostic ready: `{payload['calculator_diagnostic_ready']}`",
        f"Breaks single-shape lock: `{payload['calculator_breaks_single_shape_lock']}`",
        f"Monopole/Weyl correlation: `{payload['monopole_weyl_correlation']}`",
        f"Theta0/Doppler correlation: `{payload['theta0_doppler_quadrature_correlation']}`",
        f"Planck retry allowed: `{payload['planck_retry_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

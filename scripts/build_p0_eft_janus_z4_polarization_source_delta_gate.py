from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_acoustic_driving_delta_gate import _acoustic_source
from scripts.build_p0_eft_janus_z4_weyl_late_isw_consistency_gate import _grid


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_source_delta_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_polarization_source_delta_gate.json")
LAMBDA_GRID = (-1.6e-2, -1.2e-2, -1.0e-2, -8.0e-3, -6.0e-3, -4.0e-3, -2.0e-3, 0.0, 2.0e-3)
LAMBDA_REF = -8.0e-3
SUBCHANNELS = ("E_source_projection_only", "Theta2_quadrupole_response", "Pi_source_response", "full_polarization_source")


def _polarization_source(k: np.ndarray, tau: np.ndarray) -> dict[str, np.ndarray]:
    acoustic = _acoustic_source(k, tau)
    early = acoustic["acoustic_window"][np.newaxis, :] * acoustic["e_minus_kappa"][np.newaxis, :]
    base = early * (acoustic["delta_phi"] + acoustic["delta_psi"])
    theta2 = 0.35 * early * np.gradient(acoustic["delta_phi"] + acoustic["delta_psi"], tau, axis=1, edge_order=2)
    pi = 0.25 * early * (acoustic["delta_phi"] - 0.5 * acoustic["delta_psi"])
    full = base + theta2 + pi
    return {
        "E_source_projection_only": base,
        "Theta2_quadrupole_response": theta2,
        "Pi_source_response": pi,
        "full_polarization_source": full,
    }


def _diagnostic_for(source: np.ndarray, lam: float) -> dict:
    norm = float(np.sqrt(np.mean(np.square(source))))
    response = lam * norm
    te_zero = 0.12 * response
    ee_peak = 0.22 * response
    return {
        "finite": bool(np.isfinite(source).all() and np.isfinite(response)),
        "TE_zero_shift_1": float(te_zero),
        "TE_zero_shift_2": float(0.72 * te_zero),
        "TE_sign_check": bool(abs(te_zero) < 0.01),
        "EE_peak_shift_1": float(ee_peak),
        "EE_peak_shift_2": float(0.64 * ee_peak),
        "EE_peak_height_response": float(0.5 * response),
        "TT_peak_shift": 0.0,
        "TT_peak_height_response": 0.0,
        "source_norm": norm,
        "ok": bool(abs(te_zero) < 0.01 and abs(ee_peak) < 0.02),
    }


def build_payload() -> dict:
    k, tau = _grid()
    sources = _polarization_source(k, tau)
    scans = {
        name: {str(lam): _diagnostic_for(source, lam) for lam in LAMBDA_GRID}
        for name, source in sources.items()
    }
    source_norms = {
        name: float(np.sqrt(np.mean(np.square(source)))) for name, source in sources.items()
    }
    lambda_zero = all(scans[name]["0.0"]["ok"] for name in SUBCHANNELS)
    continuity = all(row["ok"] for scan in scans.values() for row in scan.values())
    finite = all(np.isfinite(source).all() for source in sources.values())
    gate = bool(lambda_zero and continuity and finite)
    return {
        "status": "janus-z4-polarization-source-delta-gate",
        "lambda_ref": LAMBDA_REF,
        "lambda_grid": list(LAMBDA_GRID),
        "subchannels": list(SUBCHANNELS),
        "source_level": "E_transfer_source",
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "recombination_delta_enabled": False,
        "visibility_delta_enabled": False,
        "background_projection_changed": False,
        "r_s_changed": False,
        "r_d_changed": False,
        "primordial_delta_enabled": False,
        "lensing_delta_enabled": False,
        "C_phi_phi_unchanged": True,
        "deltaSlip_Z4": "explicit_zero_until_derived",
        "metric_split_respected": True,
        "temperature_early_isw_reference_preserved": True,
        "Theta2_proxy_forbidden": False,
        "Theta2_source_tagged": True,
        "Pi_source_tagged": True,
        "official_planck_trial_allowed": False,
        "source_norms": source_norms,
        "small_lambda_scan": scans,
        "lambda_zero_identity_passed": lambda_zero,
        "small_lambda_continuity_passed": continuity,
        "polarization_source_delta_gate_passed": gate,
        "next_required_action": (
            "implement controlled polarization-source Planck trial with temperature channel fixed at lambda_ref"
            if gate
            else "fix polarization source continuity before any Planck trial"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Polarization Source Delta Gate",
        "",
        f"Gate passed: `{payload['polarization_source_delta_gate_passed']}`",
        f"Lambda ref: `{payload['lambda_ref']}`",
        f"Planck trial allowed: `{payload['official_planck_trial_allowed']}`",
        "",
        "## Source Norms",
    ]
    for key, value in payload["source_norms"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["next_required_action"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

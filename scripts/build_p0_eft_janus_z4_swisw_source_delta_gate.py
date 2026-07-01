from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_swisw_source_delta_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_swisw_source_delta_gate.json")
LAMBDAS = (0.0, 1.0e-8, 1.0e-6, 1.0e-4, 1.0e-3, 1.0e-2)


def _source_grid() -> tuple[np.ndarray, np.ndarray]:
    k = np.logspace(-4, -1, 96)
    a = np.unique(np.concatenate([np.logspace(-4, -1, 96), np.linspace(0.1, 1.0, 128)]))
    return k, a


def _late_isw_source(k: np.ndarray, a: np.ndarray) -> np.ndarray:
    kk, aa = np.meshgrid(k, a, indexing="ij")
    membrane_tail = 1.0 / (1.0 + np.exp(-(aa - 2.0 / 3.0) / 0.045))
    horizon_screen = np.exp(-np.square(kk / 0.018))
    decay = np.square(1.0 - aa) * np.exp(-2.2 * (1.0 - aa))
    return membrane_tail * horizon_screen * decay


def _early_isw_source(k: np.ndarray, a: np.ndarray) -> np.ndarray:
    kk, aa = np.meshgrid(k, a, indexing="ij")
    equality_window = np.exp(-0.5 * np.square((np.log(aa / 3.0e-4)) / 0.35))
    acoustic_screen = np.exp(-np.square(kk / 0.055))
    return equality_window * acoustic_screen


def _continuity(source: np.ndarray) -> dict[str, dict]:
    norm = float(np.sqrt(np.mean(np.square(source))))
    out = {}
    for lam in LAMBDAS:
        perturbed = lam * source
        max_abs = float(np.max(np.abs(perturbed)))
        out[str(lam)] = {
            "finite": bool(np.isfinite(perturbed).all()),
            "source_norm": float(abs(lam) * norm),
            "max_abs_source_delta": max_abs,
            "continuous": bool(max_abs < 1.0e-2),
            "ok": bool(np.isfinite(perturbed).all() and max_abs < 1.0e-2),
        }
    return out


def build_payload() -> dict:
    k, a = _source_grid()
    late = _late_isw_source(k, a)
    early = _early_isw_source(k, a)
    continuity = _continuity(late)
    late_projection = float(np.trapezoid(np.trapezoid(late, a, axis=1), np.log(k)))
    early_projection = float(np.trapezoid(np.trapezoid(early, a, axis=1), np.log(k)))
    late_support = np.trapezoid(late, a, axis=1)
    early_support = np.trapezoid(early, a, axis=1)
    late_after_membrane = float(
        np.trapezoid(np.trapezoid(late[:, a >= 2.0 / 3.0], a[a >= 2.0 / 3.0], axis=1), np.log(k))
        / max(late_projection, 1.0e-300)
    )
    early_before_recombination_tail = float(
        np.trapezoid(np.trapezoid(early[:, a <= 0.01], a[a <= 0.01], axis=1), np.log(k))
        / max(early_projection, 1.0e-300)
    )
    temporal_separation = bool(late_after_membrane > 0.70 and early_before_recombination_tail > 0.80)
    gate = bool(
        all(row["ok"] for row in continuity.values())
        and late_projection > 0.0
        and temporal_separation
    )
    return {
        "status": "janus-z4-swisw-source-delta-gate",
        "delta_channel": "late_ISW_delta",
        "delta_level": "source",
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "raw_native_los_used_for_planck": False,
        "visibility_delta_enabled": False,
        "recombination_delta_enabled": False,
        "acoustic_phase_delta_enabled": False,
        "polarization_source_delta_enabled": False,
        "primordial_spectrum_delta_enabled": False,
        "early_ISW_delta_enabled": False,
        "late_ISW_delta_enabled": True,
        "weyl_lensing_consistency_required": True,
        "lambda_zero_identity_passed": continuity["0.0"]["ok"],
        "small_lambda_continuity": continuity,
        "small_lambda_continuity_passed": all(row["ok"] for row in continuity.values()),
        "late_isw_projection_norm": late_projection,
        "early_isw_projection_norm_disabled_reference": early_projection,
        "late_isw_support_after_membrane_fraction": late_after_membrane,
        "early_isw_support_before_recombination_tail_fraction": early_before_recombination_tail,
        "late_isw_is_more_isolable_than_early_isw": temporal_separation,
        "swisw_source_delta_gate_passed": gate,
        "official_planck_trial_allowed": False,
        "next_required_action": "derive Weyl+late-ISW consistency before a second controlled Planck trial",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 SW/ISW Source Delta Gate",
        "",
        f"Gate passed: `{payload['swisw_source_delta_gate_passed']}`",
        f"Delta channel: `{payload['delta_channel']}`",
        f"Direct Cl patch: `{payload['direct_Cl_patch']}`",
        f"Late ISW enabled: `{payload['late_ISW_delta_enabled']}`",
        f"Early ISW enabled: `{payload['early_ISW_delta_enabled']}`",
        f"Planck trial allowed: `{payload['official_planck_trial_allowed']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

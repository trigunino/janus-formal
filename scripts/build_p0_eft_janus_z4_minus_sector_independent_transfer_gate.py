from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_two_sector_source_level_regeneration_gate import _source_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_independent_transfer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_independent_transfer_gate.json")
INDEPENDENCE_THRESHOLD = 0.20
WEAK_THRESHOLD = 0.05


def _best_rescale(plus: np.ndarray, minus: np.ndarray) -> tuple[float, float]:
    denom = float(np.vdot(plus, plus).real) or 1.0
    coeff = float(np.vdot(plus, minus).real / denom)
    residual = minus - coeff * plus
    return coeff, float(np.linalg.norm(residual) / (np.linalg.norm(minus) or 1.0))


def _phase_lag(plus: np.ndarray, minus: np.ndarray) -> float:
    corr = np.correlate(plus - np.mean(plus), minus - np.mean(minus), mode="full")
    return float(np.argmax(corr) - (len(plus) - 1))


def _rank_stats(plus: np.ndarray, minus: np.ndarray) -> dict:
    matrix = np.vstack([plus.ravel(), minus.ravel()])
    singular = np.linalg.svd(matrix, compute_uv=False)
    total = float(np.sum(np.square(singular))) or 1.0
    rank1 = float(np.square(singular[0]) / total)
    return {
        "singular_values": [float(x) for x in singular],
        "effective_transfer_rank": 1 if rank1 >= 0.95 else 2,
        "rank1_explained_variance": rank1,
        "rank2_residual_variance": 1.0 - rank1,
    }


def _score_pair(plus: np.ndarray, minus: np.ndarray) -> dict:
    coeff, residual = _best_rescale(plus, minus)
    ranks = _rank_stats(plus, minus)
    return {
        "minus_over_plus_amplitude_fit": coeff,
        "residual_after_best_amplitude_fit": residual,
        "phase_lag_minus_plus": _phase_lag(plus, minus),
        "k_dependence_score": 0.0,
        "tau_dependence_score": residual,
        "minus_sector_independent_transfer": residual > INDEPENDENCE_THRESHOLD and ranks["effective_transfer_rank"] == 2,
        "amplitude_rescaling_only": residual < WEAK_THRESHOLD or ranks["effective_transfer_rank"] == 1,
        **ranks,
    }


def _variables() -> dict[str, tuple[np.ndarray, np.ndarray]]:
    source = _source_payload()
    tau = np.asarray(source["time_grid"], dtype=float)
    plus = np.asarray(source["plus_drive"], dtype=float)
    minus = np.asarray(source["minus_drive"], dtype=float)
    projection = np.asarray(source["projection_window"], dtype=float)
    d_plus = np.gradient(plus, tau)
    d_minus = np.gradient(minus, tau)
    dd_plus = np.gradient(d_plus, tau)
    dd_minus = np.gradient(d_minus, tau)
    return {
        "density": (plus, minus),
        "velocity": (d_plus, d_minus),
        "shear": (dd_plus, dd_minus),
        "Weyl": (projection * plus, projection * minus),
        "Theta0": (projection * plus, projection * (plus + 0.5 * minus)),
        "Pi": (projection * (0.15 * plus), projection * (0.35 * (plus - minus) + 0.15 * plus)),
        "projection_source": (projection * plus, projection * minus),
    }


def build_payload() -> dict:
    rows = {name: _score_pair(plus, minus) for name, (plus, minus) in _variables().items()}
    independent = [name for name, row in rows.items() if row["minus_sector_independent_transfer"]]
    amplitude_only = [name for name, row in rows.items() if row["amplitude_rescaling_only"]]
    return {
        "status": "janus-z4-minus-sector-independent-transfer-gate",
        "transfer_rows": rows,
        "independent_transfer_components": independent,
        "amplitude_rescaling_components": amplitude_only,
        "any_minus_sector_independent_transfer": bool(independent),
        "minus_sector_transfer_independent": bool(independent),
        "minus_sound_speed_differs_from_plus": False,
        "minus_pressure_differs_from_plus": False,
        "minus_shear_differs_from_plus": "shear" in independent,
        "minus_free_streaming_differs_from_plus": False,
        "minus_recombination_or_decoupling_differs_from_plus": False,
        "minus_temperature_ratio_declared": False,
        "minus_initial_mode_phase_lag": max(abs(row["phase_lag_minus_plus"]) for row in rows.values()),
        "antisymmetric_mode_phase_survives": any(abs(row["phase_lag_minus_plus"]) > 0 for row in rows.values()),
        "no_rho_eff_shortcut": True,
        "direct_Cl_patch_forbidden": True,
        "raw_toy_LOS_forbidden": True,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "projection_retuning_allowed": False,
        "free_minus_amplitude_allowed": False,
        "hidden_rescaling_coefficient_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MinusIndependentComponentGate" if independent else "derive_minus_sector_microphysics",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Minus-Sector Independent Transfer Gate",
        "",
        f"Independent components: `{payload['independent_transfer_components']}`",
        f"Amplitude-rescaling components: `{payload['amplitude_rescaling_components']}`",
        f"Minus transfer independent: `{payload['minus_sector_transfer_independent']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

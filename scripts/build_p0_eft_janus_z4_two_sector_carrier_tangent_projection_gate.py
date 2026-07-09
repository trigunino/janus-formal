from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import (
    CHANNELS,
    _projection_stats,
    _tangent_matrix,
)
from scripts.build_p0_eft_janus_z4_two_sector_source_level_regeneration_gate import _source_payload, build_payload as source_payload
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_carrier_tangent_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_carrier_tangent_projection_gate.json")


def _interp(values: list[float], ells: np.ndarray) -> np.ndarray:
    x = np.linspace(float(ells[0]), float(ells[-1]), len(values))
    return np.interp(ells, x, np.asarray(values, dtype=float))


def _unit(v: np.ndarray) -> np.ndarray:
    return v / (float(np.max(np.abs(v))) or 1.0)


def _delta(reference: list[dict[str, float]], source: dict, channel: str) -> dict[str, np.ndarray]:
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    zero = np.zeros_like(ell)
    if channel == "weyl":
        shape = _unit(_interp(source["deltaWeyl_plus_observable"], ell))
        return {"cl_tt": arrays["cl_tt"] * shape, "cl_te": 0.5 * arrays["cl_te"] * shape, "cl_ee": zero}
    if channel == "theta0":
        shape = _unit(_interp(source["Theta0_two_sector_projection"], ell))
        return {"cl_tt": arrays["cl_tt"] * shape, "cl_te": 0.25 * arrays["cl_te"] * shape, "cl_ee": zero}
    if channel == "pi":
        shape = _unit(_interp(source["Pi_two_sector_projection"], ell))
        return {"cl_tt": zero, "cl_te": 0.5 * arrays["cl_te"] * shape, "cl_ee": arrays["cl_ee"] * shape}
    if channel == "full_two_sector":
        weyl = _delta(reference, source, "weyl")
        theta = _delta(reference, source, "theta0")
        pi = _delta(reference, source, "pi")
        return {key: weyl[key] + theta[key] + pi[key] for key in CHANNELS}
    raise ValueError(channel)


def _classification(parallel: float) -> str:
    if parallel > 0.8:
        return "closure_recommended"
    if parallel >= 0.5:
        return "diagnostic_only"
    return "candidate_path_possible"


def build_payload() -> dict:
    source_gate = source_payload()
    source = _source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    rows = {}
    for channel in ("weyl", "theta0", "pi", "full_two_sector"):
        rows[channel] = _projection_stats(_flatten(_delta(reference, source, channel), scales), matrix, tangent_norms)
    full_parallel = rows["full_two_sector"]["parallel_fraction"]
    return {
        "status": "janus-z4-two-sector-carrier-tangent-projection-gate",
        "source_level_regeneration_gate_passed": bool(source_gate["carrier_tangent_projection_allowed"]),
        "projected_channels": rows,
        "parallel_fraction_weyl": rows["weyl"]["parallel_fraction"],
        "parallel_fraction_theta0": rows["theta0"]["parallel_fraction"],
        "parallel_fraction_pi": rows["pi"]["parallel_fraction"],
        "parallel_fraction_full_two_sector": full_parallel,
        "perpendicular_fraction_full_two_sector": rows["full_two_sector"]["perpendicular_fraction"],
        "dominant_tangent_direction_full_two_sector": rows["full_two_sector"]["dominant_tangent_direction"],
        "classification": _classification(full_parallel),
        "candidate_path_possible": full_parallel < 0.5,
        "diagnostic_only": 0.5 <= full_parallel <= 0.8,
        "closure_recommended": full_parallel > 0.8,
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "rho_eff_shortcut_forbidden": True,
        "direct_Cl_patch_forbidden": True,
        "raw_toy_LOS_forbidden": True,
        "next_required_gate": "P0EFTJanusZ4TwoSectorResidualDiagnosticGate" if full_parallel < 0.5 else "close_or_refine_two_sector_source",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Two-Sector Carrier Tangent Projection Gate",
        "",
        f"Full two-sector parallel: `{payload['parallel_fraction_full_two_sector']}`",
        f"Classification: `{payload['classification']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _projection_stats, _tangent_matrix
from scripts.build_p0_eft_janus_z4_two_sector_source_level_regeneration_gate import _source_payload
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_source_construction_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_source_construction_audit_gate.json")


def _interp(values: list[float], ells: np.ndarray) -> np.ndarray:
    x = np.linspace(float(ells[0]), float(ells[-1]), len(values))
    return np.interp(ells, x, np.asarray(values, dtype=float))


def _unit(v: np.ndarray) -> np.ndarray:
    return v / (float(np.max(np.abs(v))) or 1.0)


def _delta(reference: list[dict[str, float]], shape: np.ndarray, kind: str) -> dict[str, np.ndarray]:
    arrays = _rows_to_arrays(reference)
    zero = np.zeros_like(shape)
    if kind == "temperature":
        return {"cl_tt": arrays["cl_tt"] * shape, "cl_te": 0.5 * arrays["cl_te"] * shape, "cl_ee": zero}
    if kind == "polarization":
        return {"cl_tt": zero, "cl_te": 0.5 * arrays["cl_te"] * shape, "cl_ee": arrays["cl_ee"] * shape}
    return {"cl_tt": arrays["cl_tt"] * shape, "cl_te": arrays["cl_te"] * shape, "cl_ee": arrays["cl_ee"] * shape}


def build_payload() -> dict:
    source = _source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    ell = arrays["ell"]
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    component_specs = {
        "plus_only_source": ("plus_drive", "temperature"),
        "minus_only_source": ("minus_drive", "temperature"),
        "symmetric_mode_source": ("plus_drive", "all"),
        "antisymmetric_Z4_mode_source": ("antisymmetric_Z4_drive", "temperature"),
        "relative_isocurvature_mode_source": ("antisymmetric_Z4_drive", "all"),
        "projection_only_source": ("projection_window", "temperature"),
        "Weyl_source": ("deltaWeyl_plus_observable", "temperature"),
        "Theta0_source": ("Theta0_two_sector_projection", "temperature"),
        "Pi_source": ("Pi_two_sector_projection", "polarization"),
    }
    rows = {}
    for name, (key, kind) in component_specs.items():
        shape = _unit(_interp(source[key], ell))
        rows[name] = _projection_stats(_flatten(_delta(reference, shape, kind), scales), matrix, tangent_norms)
    survivors = [name for name, stats in rows.items() if stats["parallel_fraction"] < 0.7]
    return {
        "status": "janus-z4-two-sector-source-construction-audit-gate",
        "component_projection_rows": rows,
        "surviving_components_parallel_lt_0p7": survivors,
        "any_component_survives": bool(survivors),
        "antisymmetric_Z4_mode_survives_projection": "antisymmetric_Z4_mode_source" in survivors,
        "relative_isocurvature_survives_projection": "relative_isocurvature_mode_source" in survivors,
        "minus_sector_collapses_to_amplitude_rescaling": rows["minus_only_source"]["parallel_fraction"] >= 0.8,
        "projection_matrix_erases_Z4_antisymmetry": rows["antisymmetric_Z4_mode_source"]["parallel_fraction"] >= 0.8,
        "full_source_archived": True,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4AntisymmetricModeSourceGate" if "antisymmetric_Z4_mode_source" in survivors else "revisit_projection_or_sector_minus_dynamics",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Two-Sector Source Construction Audit Gate",
        "",
        f"Any component survives <0.7: `{payload['any_component_survives']}`",
        f"Survivors: `{payload['surviving_components_parallel_lt_0p7']}`",
        f"Antisymmetric survives: `{payload['antisymmetric_Z4_mode_survives_projection']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

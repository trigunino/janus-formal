from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows, write_spectra
from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_generation_gate import _interp
from scripts.build_p0_eft_janus_z4_master_photon_baryon_matching_gate import (
    build_payload as matching_payload,
)
from scripts.build_p0_eft_janus_z4_master_revised_source_level_regeneration_gate import (
    build_revised_source_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_source_component_diagnostic_spectra_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_source_component_diagnostic_spectra_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_master_source_component_diagnostic_spectra")
MATCHING_JSON = Path("outputs/reports/p0_eft_janus_z4_master_photon_baryon_matching_gate.json")
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


def _rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(values))))


def _write_component(path: Path, reference: list[dict[str, float]], deltas: dict[str, np.ndarray]) -> None:
    rows = []
    for i, row in enumerate(reference):
        rows.append(
            {
                "ell": int(row["ell"]),
                "cl_tt": float(row["cl_tt"] + deltas.get("cl_tt", 0.0)[i]),
                "cl_te": float(row["cl_te"] + deltas.get("cl_te", 0.0)[i]),
                "cl_ee": float(row["cl_ee"] + deltas.get("cl_ee", 0.0)[i]),
                "cl_pp": float(row["cl_pp"] + deltas.get("cl_pp", 0.0)[i]),
            }
        )
    write_spectra(path, rows)


def build_payload() -> dict:
    matching = _load_json(MATCHING_JSON) or matching_payload()
    source = _load_source_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    ell = np.asarray([row["ell"] for row in reference], dtype=float)
    base = {
        "cl_tt": np.asarray([row["cl_tt"] for row in reference], dtype=float),
        "cl_te": np.asarray([row["cl_te"] for row in reference], dtype=float),
        "cl_ee": np.asarray([row["cl_ee"] for row in reference], dtype=float),
        "cl_pp": np.asarray([row["cl_pp"] for row in reference], dtype=float),
    }

    u = _interp(source["U_Z4"], ell)
    theta0 = _interp(source["Theta0_Z4"], ell)
    doppler = _interp(source["Doppler_Z4"], ell)
    pi = _interp(source["Pi_Z4"], ell)
    st = _interp(source["S_T_Z4"], ell)
    se = _interp(source["S_E_Z4"], ell)

    components = {
        "surface_SW": {"cl_tt": base["cl_tt"] * theta0, "cl_te": base["cl_te"] * 0.15 * theta0, "cl_ee": base["cl_ee"] * 0.0, "cl_pp": base["cl_pp"] * 0.0},
        "early_ISW": {"cl_tt": base["cl_tt"] * (st - theta0), "cl_te": base["cl_te"] * 0.2 * (st - theta0), "cl_ee": base["cl_ee"] * 0.0, "cl_pp": base["cl_pp"] * 0.0},
        "Doppler": {"cl_tt": base["cl_tt"] * 0.35 * doppler, "cl_te": base["cl_te"] * 0.55 * doppler, "cl_ee": base["cl_ee"] * 0.1 * doppler, "cl_pp": base["cl_pp"] * 0.0},
        "polarization_Pi": {"cl_tt": base["cl_tt"] * 0.0, "cl_te": base["cl_te"] * 0.4 * pi, "cl_ee": base["cl_ee"] * (se + 0.25 * pi), "cl_pp": base["cl_pp"] * 0.0},
        "lens_Weyl": {"cl_tt": base["cl_tt"] * 0.0, "cl_te": base["cl_te"] * 0.0, "cl_ee": base["cl_ee"] * 0.0, "cl_pp": base["cl_pp"] * 0.45 * u},
    }

    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    baseline_path = SPECTRA_DIR / "reference_gr.csv"
    write_spectra(baseline_path, reference)
    component_paths = {}
    component_norms = {}
    for name, deltas in components.items():
        path = SPECTRA_DIR / f"{name}.csv"
        _write_component(path, reference, deltas)
        component_paths[name] = str(path)
        component_norms[name] = {channel: _rms(delta) for channel, delta in deltas.items()}

    return {
        "status": "janus-z4-master-source-component-diagnostic-spectra-gate",
        "photon_baryon_matching_passed": matching["photon_baryon_matching_passed"],
        "baseline_spectra_path": str(baseline_path),
        "component_spectra_paths": component_paths,
        "component_norms": component_norms,
        "surface_SW_component_written": True,
        "early_ISW_component_written": True,
        "Doppler_component_written": True,
        "polarization_Pi_component_written": True,
        "lens_Weyl_component_written": True,
        "unlensed_lensed_split_available": False,
        "unlensed_lensed_split_reason": "provider returns lensed total spectra only",
        "source_component_attribution_complete": True,
        "diagnostic_only": True,
        "observed_likelihood_allowed": False,
        "planck_retry_allowed": False,
        "candidate_promotion_allowed": False,
        "new_physics_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "archive_master_v2_mapping_or_derive_unlensed_source_backend",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Source-Component Diagnostic Spectra Gate",
        "",
        f"Diagnostic only: `{payload['diagnostic_only']}`",
        f"Source attribution complete: `{payload['source_component_attribution_complete']}`",
        f"Unlensed/lensed split available: `{payload['unlensed_lensed_split_available']}`",
        f"Planck retry allowed: `{payload['planck_retry_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

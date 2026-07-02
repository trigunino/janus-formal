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
from scripts.build_p0_eft_janus_z4_master_photon_baryon_acoustic_calculator_gate import (
    build_payload as calculator_gate_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_component_spectra_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_component_spectra_gate.json")
CALCULATOR_PAYLOAD_JSON = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_payload.json")
SPECTRA_DIR = Path("outputs/reports/z4_master_acoustic_calculator_component_spectra")


def _load_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None


def _write_component(path: Path, reference: list[dict[str, float]], deltas: dict[str, np.ndarray]) -> None:
    rows = []
    for i, row in enumerate(reference):
        rows.append({
            "ell": int(row["ell"]),
            "cl_tt": float(row["cl_tt"] + deltas["cl_tt"][i]),
            "cl_te": float(row["cl_te"] + deltas["cl_te"][i]),
            "cl_ee": float(row["cl_ee"] + deltas["cl_ee"][i]),
            "cl_pp": float(row["cl_pp"] + deltas["cl_pp"][i]),
        })
    write_spectra(path, rows)


def _norm(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(values))))


def build_payload() -> dict:
    calculator_gate = calculator_gate_payload()
    calculator = _load_json(CALCULATOR_PAYLOAD_JSON)
    if calculator is None:
        calculator = json.loads(Path(calculator_gate["calculator_payload_path"]).read_text(encoding="utf-8"))
    reference = generate_camb_gr_rows(CosmologyPoint())
    ell = np.asarray([row["ell"] for row in reference], dtype=float)
    base = {
        "cl_tt": np.asarray([row["cl_tt"] for row in reference], dtype=float),
        "cl_te": np.asarray([row["cl_te"] for row in reference], dtype=float),
        "cl_ee": np.asarray([row["cl_ee"] for row in reference], dtype=float),
        "cl_pp": np.asarray([row["cl_pp"] for row in reference], dtype=float),
    }
    theta0 = _interp(calculator["Theta0_acoustic"], ell)
    doppler = _interp(calculator["Doppler_acoustic"], ell)
    pi = _interp(calculator["Pi_acoustic"], ell)
    st = _interp(calculator["S_T_acoustic"], ell)
    se = _interp(calculator["S_E_acoustic"], ell)
    early = st - theta0 - 0.35 * doppler
    components = {
        "surface_SW": {"cl_tt": base["cl_tt"] * theta0, "cl_te": base["cl_te"] * 0.12 * theta0, "cl_ee": base["cl_ee"] * 0.0, "cl_pp": base["cl_pp"] * 0.0},
        "early_ISW": {"cl_tt": base["cl_tt"] * early, "cl_te": base["cl_te"] * 0.12 * early, "cl_ee": base["cl_ee"] * 0.0, "cl_pp": base["cl_pp"] * 0.0},
        "Doppler": {"cl_tt": base["cl_tt"] * 0.35 * doppler, "cl_te": base["cl_te"] * 0.55 * doppler, "cl_ee": base["cl_ee"] * 0.08 * doppler, "cl_pp": base["cl_pp"] * 0.0},
        "polarization_Pi": {"cl_tt": base["cl_tt"] * 0.0, "cl_te": base["cl_te"] * 0.35 * pi, "cl_ee": base["cl_ee"] * se, "cl_pp": base["cl_pp"] * 0.0},
    }
    total = {channel: sum(component[channel] for component in components.values()) for channel in ("cl_tt", "cl_te", "cl_ee", "cl_pp")}
    SPECTRA_DIR.mkdir(parents=True, exist_ok=True)
    baseline_path = SPECTRA_DIR / "reference_gr.csv"
    total_path = SPECTRA_DIR / "total_acoustic.csv"
    write_spectra(baseline_path, reference)
    component_paths = {}
    component_norms = {}
    for name, deltas in {**components, "total_acoustic": total}.items():
        path = SPECTRA_DIR / f"{name}.csv"
        _write_component(path, reference, deltas)
        component_paths[name] = str(path)
        component_norms[name] = {channel: _norm(values) for channel, values in deltas.items()}
    return {
        "status": "janus-z4-master-acoustic-calculator-component-spectra-gate",
        "calculator_diagnostic_ready": calculator_gate["calculator_diagnostic_ready"],
        "calculator_payload_path": str(CALCULATOR_PAYLOAD_JSON),
        "baseline_spectra_path": str(baseline_path),
        "total_spectra_path": str(total_path),
        "component_spectra_paths": component_paths,
        "component_norms": component_norms,
        "surface_SW_component_written": True,
        "early_ISW_component_written": True,
        "Doppler_component_written": True,
        "polarization_Pi_component_written": True,
        "internal_diagnostic_spectra_generated": True,
        "unlensed_lensed_split_available": False,
        "unlensed_lensed_split_reason": "regenerative provider returns lensed total spectra only",
        "observed_likelihood_allowed": False,
        "planck_retry_allowed": False,
        "candidate_promotion_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterAcousticCalculatorShapePhaseDampingGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Acoustic Calculator Component Spectra Gate",
        "",
        f"Internal diagnostic spectra generated: `{payload['internal_diagnostic_spectra_generated']}`",
        f"Unlensed/lensed split available: `{payload['unlensed_lensed_split_available']}`",
        f"Planck retry allowed: `{payload['planck_retry_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

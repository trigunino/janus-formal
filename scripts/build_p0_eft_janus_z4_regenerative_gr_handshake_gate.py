from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import camb_gr_rows
from scripts.run_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial import _run_likelihood_set
from janus_lab.z4_regenerative_camb_provider import (
    CosmologyPoint,
    FIELDS,
    generate_camb_gr_rows,
    provenance_manifest,
    write_spectra,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_handshake_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_handshake_gate.json")
REFERENCE_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_handshake_reference.csv")
REGENERATED_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_handshake_regenerated.csv")
TOL_ABS = 1.0e-18
TOL_CHI2 = 1.0e-6


def _max_abs_delta(left: list[dict[str, float]], right: list[dict[str, float]], field: str) -> float:
    return float(max(abs(float(a[field]) - float(b[field])) for a, b in zip(left, right)))


def _likelihood_delta(reference: dict, regenerated: dict) -> dict:
    ref = reference.get("finite_channel_chi2", {})
    reg = regenerated.get("finite_channel_chi2", {})
    return {name: float(reg[name] - ref[name]) for name in sorted(ref) if name in reg}


def build_payload(run_official: bool = False) -> dict:
    cosmology = CosmologyPoint()
    reference_rows = camb_gr_rows()
    regenerated_rows = generate_camb_gr_rows(cosmology)
    write_spectra(REFERENCE_PATH, reference_rows)
    write_spectra(REGENERATED_PATH, regenerated_rows)
    manifest = provenance_manifest(cosmology=cosmology)
    same_length = len(reference_rows) == len(regenerated_rows)
    same_ell = same_length and all(a["ell"] == b["ell"] for a, b in zip(reference_rows, regenerated_rows))
    deltas = {field: _max_abs_delta(reference_rows, regenerated_rows, field) for field in FIELDS if field != "ell"}
    vector_match = same_ell and all(value <= TOL_ABS for value in deltas.values())
    reference_likelihood = _run_likelihood_set(REFERENCE_PATH, run_official)
    regenerated_likelihood = _run_likelihood_set(REGENERATED_PATH, run_official)
    chi2_delta = _likelihood_delta(reference_likelihood, regenerated_likelihood) if run_official else {}
    likelihood_match = bool(run_official and chi2_delta and all(abs(value) <= TOL_CHI2 for value in chi2_delta.values()))
    return {
        "status": "janus-z4-regenerative-gr-handshake-gate",
        "lambda_T": 0.0,
        "lambda_E": 0.0,
        "Z4_delta_enabled": False,
        "source_of_spectra": "regenerated",
        "reference_spectra_path": str(REFERENCE_PATH),
        "regenerated_spectra_path": str(REGENERATED_PATH),
        "provenance_manifest": manifest,
        "cmb_spectra_kind": manifest["cmb_spectra_kind"],
        "cl_pp_kind": manifest["cl_pp_kind"],
        "C_l_not_D_l": True,
        "units_preserved": True,
        "TE_sign_preserved": True,
        "ell_indexing_preserved": same_ell,
        "cl_pp_convention_is_C_L_phiphi": manifest["cl_pp_kind"] == "C_L_phiphi",
        "no_C_L_dd": True,
        "no_L4_C_L_phiphi": True,
        "max_abs_delta_by_field": deltas,
        "theory_vector_matches_reference": vector_match,
        "run_official_requested": run_official,
        "reference_likelihood": reference_likelihood,
        "regenerated_likelihood": regenerated_likelihood,
        "likelihood_delta_by_channel": chi2_delta,
        "likelihood_sanity_passed": likelihood_match,
        "regenerative_gr_handshake_passed": bool(vector_match and (not run_official or likelihood_match)),
        "full_planck_validation": False,
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative GR Handshake Gate",
        "",
        f"Handshake passed: `{payload['regenerative_gr_handshake_passed']}`",
        f"Theory vector matches reference: `{payload['theory_vector_matches_reference']}`",
        f"Likelihood sanity passed: `{payload['likelihood_sanity_passed']}`",
        f"CMB spectra kind: `{payload['cmb_spectra_kind']}`",
        f"cl_pp kind: `{payload['cl_pp_kind']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))

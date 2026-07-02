from __future__ import annotations

import json
import sys
from dataclasses import asdict, replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_candidate_local_cosmology_profiling_gate import (
    COMBINED_CHANNELS,
    DECOMPOSED_CHANNELS,
    _delta_channels,
    _total,
)
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import (
    FROZEN_LAMBDA_E,
    FROZEN_LAMBDA_T,
    _write_candidate,
)
from scripts.run_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial import _run_likelihood_set
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows, write_spectra


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_local_2d_carrier_profiling_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_local_2d_carrier_profiling_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_local_2d_carrier_profile_spectra")

PAIR_SHIFTS = {
    "omega_cdm_x_A_s": ({"omch2": 0.1205}, {"As": 2.142e-9}),
    "omega_cdm_x_n_s": ({"omch2": 0.1205}, {"ns": 0.970}),
    "omega_cdm_x_H0": ({"omch2": 0.1205}, {"H0": 67.9}),
    "omega_cdm_x_omega_b": ({"omch2": 0.1205}, {"ombh2": 0.02247}),
}


def _safe_name(name: str) -> str:
    return name.replace(".", "p").replace("-", "m")


def _write_pair(name: str, cosmology: CosmologyPoint) -> tuple[Path, Path]:
    rows = generate_camb_gr_rows(cosmology)
    baseline_path = SPECTRA_DIR / f"{_safe_name(name)}__gr.csv"
    candidate_path = SPECTRA_DIR / f"{_safe_name(name)}__z4.csv"
    write_spectra(baseline_path, rows)
    _write_candidate(rows, FROZEN_LAMBDA_T, FROZEN_LAMBDA_E, candidate_path)
    return baseline_path, candidate_path


def _basis_totals(like: dict) -> dict:
    return {
        "combined_highl": _total(like, COMBINED_CHANNELS),
        "decomposed_highl": _total(like, DECOMPOSED_CHANNELS),
    }


def _grid_for_pair(pair: str, first: dict, second: dict) -> dict[str, CosmologyPoint]:
    base = CosmologyPoint()
    both = {**first, **second}
    return {
        f"{pair}__reference": base,
        f"{pair}__omega_cdm": replace(base, **first),
        f"{pair}__partner": replace(base, **second),
        f"{pair}__joint": replace(base, **both),
    }


def build_payload(run_official: bool = False) -> dict:
    pair_rows = {}
    for pair, (first, second) in PAIR_SHIFTS.items():
        rows = {}
        if run_official:
            for key, cosmology in _grid_for_pair(pair, first, second).items():
                baseline_path, candidate_path = _write_pair(key, cosmology)
                gr_like = _run_likelihood_set(baseline_path, True)
                cand_like = _run_likelihood_set(candidate_path, True)
                gr_totals = _basis_totals(gr_like)
                cand_totals = _basis_totals(cand_like)
                rows[key] = {
                    "cosmology": asdict(cosmology),
                    "baseline_spectra_path": str(baseline_path),
                    "candidate_spectra_path": str(candidate_path),
                    "GR_totals": gr_totals,
                    "candidate_totals": cand_totals,
                    "delta_totals": {
                        basis: float(cand_totals[basis] - gr_totals[basis])
                        for basis in gr_totals
                        if cand_totals[basis] is not None and gr_totals[basis] is not None
                    },
                    "delta_chi2_by_channel": _delta_channels(cand_like, gr_like),
                }
        summaries = {}
        for basis in ("combined_highl", "decomposed_highl"):
            if rows:
                gr_best_key = min(rows, key=lambda key: rows[key]["GR_totals"][basis])
                cand_best_key = min(rows, key=lambda key: rows[key]["candidate_totals"][basis])
                summaries[basis] = {
                    "bestfit_GR_grid_key": gr_best_key,
                    "bestfit_candidate_grid_key": cand_best_key,
                    "candidate_gain_after_2d_carrier_profile": float(
                        rows[cand_best_key]["candidate_totals"][basis] - rows[gr_best_key]["GR_totals"][basis]
                    ),
                    "candidate_gain_at_reference": rows[f"{pair}__reference"]["delta_totals"][basis],
                }
            else:
                summaries[basis] = {}
        pair_rows[pair] = {
            "pair": pair,
            "grid_rows": rows,
            "summaries": summaries,
            "pair_gain_survives": bool(
                run_official
                and summaries["combined_highl"].get("candidate_gain_after_2d_carrier_profile", 0.0) < 0.0
                and summaries["decomposed_highl"].get("candidate_gain_after_2d_carrier_profile", 0.0) < 0.0
            ),
        }
    gate_passed = bool(run_official and all(row["pair_gain_survives"] for row in pair_rows.values()))
    return {
        "status": "janus-z4-local-2d-carrier-profiling-gate",
        "run_official_requested": run_official,
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "lambda_frozen": True,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "same_grid_for_GR_and_candidate": True,
        "non_overlap_accounting_only": True,
        "pairs_tested": list(PAIR_SHIFTS),
        "pair_rows": pair_rows,
        "all_2d_pair_gains_survive": gate_passed,
        "local_2d_carrier_profiled_effective_candidate": gate_passed,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Local 2D Carrier Profiling Gate",
        "",
        f"Gate passed: `{payload['all_2d_pair_gains_survive']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    for pair, row in payload["pair_rows"].items():
        lines.append(f"- `{pair}` survives: `{row['pair_gain_survives']}`")
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))

from __future__ import annotations

import json
import sys
from dataclasses import asdict, replace
from pathlib import Path

import numpy as np

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


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_carrier_parameter_degeneracy_report.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_carrier_parameter_degeneracy_report.json")
SPECTRA_DIR = Path("outputs/reports/z4_carrier_parameter_degeneracy_spectra")
OMEGA_CDM_GRID = (0.1190, 0.1195, 0.1200, 0.1205, 0.1210)


def _write_pair(omch2: float) -> tuple[Path, Path]:
    cosmology = replace(CosmologyPoint(), omch2=omch2)
    rows = generate_camb_gr_rows(cosmology)
    tag = f"omch2_{omch2:.4f}".replace(".", "p")
    baseline_path = SPECTRA_DIR / f"{tag}__gr.csv"
    candidate_path = SPECTRA_DIR / f"{tag}__z4.csv"
    write_spectra(baseline_path, rows)
    _write_candidate(rows, FROZEN_LAMBDA_T, FROZEN_LAMBDA_E, candidate_path)
    return baseline_path, candidate_path


def _basis_totals(like: dict) -> dict:
    return {
        "combined_highl": _total(like, COMBINED_CHANNELS),
        "decomposed_highl": _total(like, DECOMPOSED_CHANNELS),
    }


def _curvature(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) < 3:
        return None
    coeff = np.polyfit(np.array(xs, dtype=float), np.array(ys, dtype=float), 2)
    return float(2.0 * coeff[0])


def _corr(a: list[float], b: list[float]) -> float | None:
    aa = np.array(a, dtype=float)
    bb = np.array(b, dtype=float)
    if np.std(aa) == 0.0 or np.std(bb) == 0.0:
        return None
    return float(np.corrcoef(aa, bb)[0, 1])


def build_payload(run_official: bool = False) -> dict:
    rows = []
    for omch2 in OMEGA_CDM_GRID:
        if not run_official:
            continue
        baseline_path, candidate_path = _write_pair(omch2)
        gr_like = _run_likelihood_set(baseline_path, True)
        candidate_like = _run_likelihood_set(candidate_path, True)
        gr_totals = _basis_totals(gr_like)
        candidate_totals = _basis_totals(candidate_like)
        rows.append(
            {
                "omega_cdm": omch2,
                "cosmology": asdict(replace(CosmologyPoint(), omch2=omch2)),
                "baseline_spectra_path": str(baseline_path),
                "candidate_spectra_path": str(candidate_path),
                "GR_totals": gr_totals,
                "candidate_totals": candidate_totals,
                "delta_totals": {
                    key: float(candidate_totals[key] - gr_totals[key])
                    for key in gr_totals
                    if candidate_totals[key] is not None and gr_totals[key] is not None
                },
                "delta_chi2_by_channel": _delta_channels(candidate_like, gr_like),
            }
        )
    summaries = {}
    for basis in ("combined_highl", "decomposed_highl"):
        if rows:
            gr_values = [row["GR_totals"][basis] for row in rows]
            cand_values = [row["candidate_totals"][basis] for row in rows]
            deltas = [row["delta_totals"][basis] for row in rows]
            gr_best_i = int(np.argmin(gr_values))
            cand_best_i = int(np.argmin(cand_values))
            summaries[basis] = {
                "bestfit_GR_omega_cdm": rows[gr_best_i]["omega_cdm"],
                "bestfit_candidate_omega_cdm": rows[cand_best_i]["omega_cdm"],
                "bestfit_omega_cdm_shift": float(rows[cand_best_i]["omega_cdm"] - rows[gr_best_i]["omega_cdm"]),
                "GR_curvature_omega_cdm": _curvature([row["omega_cdm"] for row in rows], gr_values),
                "candidate_curvature_omega_cdm": _curvature([row["omega_cdm"] for row in rows], cand_values),
                "candidate_gain_after_marginalizing_omega_cdm": float(min(cand_values) - min(gr_values)),
                "candidate_gain_at_reference_omega_cdm": next(row["delta_totals"][basis] for row in rows if row["omega_cdm"] == 0.1200),
                "correlation_like_score_GR_vs_candidate_profile": _corr(gr_values, cand_values),
                "delta_chi2_values": deltas,
            }
        else:
            summaries[basis] = {}
    survives = bool(
        run_official
        and summaries["combined_highl"].get("candidate_gain_after_marginalizing_omega_cdm", 0.0) < 0.0
        and summaries["decomposed_highl"].get("candidate_gain_after_marginalizing_omega_cdm", 0.0) < 0.0
    )
    return {
        "status": "janus-z4-carrier-parameter-degeneracy-report",
        "focus_parameter": "omega_cdm",
        "run_official_requested": run_official,
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "lambda_frozen": True,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "omega_cdm_grid": list(OMEGA_CDM_GRID),
        "rows": rows,
        "summaries": summaries,
        "gain_survives_omega_cdm_marginalization": survives,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Carrier Parameter Degeneracy Report",
        "",
        f"Focus parameter: `{payload['focus_parameter']}`",
        f"Gain survives omega_cdm marginalization: `{payload['gain_survives_omega_cdm_marginalization']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    for basis, summary in payload["summaries"].items():
        lines.append(
            f"- `{basis}`: gain after omega_cdm marginalization "
            f"`{summary.get('candidate_gain_after_marginalizing_omega_cdm')}`"
        )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))

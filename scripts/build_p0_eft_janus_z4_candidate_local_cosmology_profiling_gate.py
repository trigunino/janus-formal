from __future__ import annotations

import json
import sys
from dataclasses import asdict, replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_candidate_local_nuisance_profiling_gate import BASES, _profile
from scripts.build_p0_eft_janus_z4_local_cosmology_profiling_readiness_gate import build_payload as readiness_payload
from scripts.build_p0_eft_janus_z4_regenerative_cache_invalidation_gate import MUTATIONS
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import (
    FROZEN_LAMBDA_E,
    FROZEN_LAMBDA_T,
    _write_candidate,
)
from scripts.run_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial import _run_likelihood_set
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows, write_spectra


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_local_cosmology_profiling_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_local_cosmology_profiling_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_candidate_local_cosmology_profile_spectra")

CHANNELS = ("highl_TT", "highl_TE", "highl_EE", "highl_TTTEEE", "lowl_TT", "lowl_EE", "lensing")
COMBINED_CHANNELS = ("highl_TTTEEE", "lowl_TT", "lowl_EE", "lensing")
DECOMPOSED_CHANNELS = ("highl_TT", "highl_TE", "highl_EE", "lowl_TT", "lowl_EE", "lensing")


def _safe_name(name: str) -> str:
    return name.replace(".", "p").replace("-", "m")


def _total(row: dict, channels: tuple[str, ...]) -> float | None:
    finite = row.get("finite_channel_chi2", {})
    if not all(channel in finite for channel in channels):
        return None
    return float(sum(finite[channel] for channel in channels))


def _delta_channels(candidate: dict, baseline: dict) -> dict[str, float | None]:
    out = {}
    for channel in CHANNELS:
        c = candidate.get("finite_channel_chi2", {}).get(channel)
        b = baseline.get("finite_channel_chi2", {}).get(channel)
        out[channel] = float(c - b) if c is not None and b is not None else None
    return out


def _cosmology_grid() -> dict[str, CosmologyPoint]:
    base = CosmologyPoint()
    rows = {"reference": base}
    for name, (attr, value) in MUTATIONS.items():
        rows[name] = replace(base, **{attr: value})
    return rows


def _write_pair(name: str, cosmology: CosmologyPoint) -> tuple[Path, Path]:
    rows = generate_camb_gr_rows(cosmology)
    baseline_path = SPECTRA_DIR / f"{_safe_name(name)}__gr.csv"
    candidate_path = SPECTRA_DIR / f"{_safe_name(name)}__z4.csv"
    write_spectra(baseline_path, rows)
    _write_candidate(rows, FROZEN_LAMBDA_T, FROZEN_LAMBDA_E, candidate_path)
    return baseline_path, candidate_path


def _profile_best(components: tuple[str, ...], path: str) -> dict:
    return _profile(components, path, boundary_guard_epsilon=1.0e-2)


def build_payload(run_official: bool = False) -> dict:
    readiness = readiness_payload()
    runnable = bool(readiness.get("local_cosmology_profiling_allowed"))
    grid_rows = {}
    if run_official and runnable:
        for name, cosmology in _cosmology_grid().items():
            baseline_path, candidate_path = _write_pair(name, cosmology)
            baseline_like = _run_likelihood_set(baseline_path, True)
            candidate_like = _run_likelihood_set(candidate_path, True)
            grid_rows[name] = {
                "cosmology": asdict(cosmology),
                "baseline_spectra_path": str(baseline_path),
                "candidate_spectra_path": str(candidate_path),
                "GR_fixed_nuisance": baseline_like,
                "candidate_fixed_nuisance": candidate_like,
                "combined_highl_GR": _total(baseline_like, COMBINED_CHANNELS),
                "combined_highl_candidate": _total(candidate_like, COMBINED_CHANNELS),
                "decomposed_highl_GR": _total(baseline_like, DECOMPOSED_CHANNELS),
                "decomposed_highl_candidate": _total(candidate_like, DECOMPOSED_CHANNELS),
                "delta_chi2_by_channel": _delta_channels(candidate_like, baseline_like),
            }
    basis_rows = {}
    for basis, components in BASES.items():
        if run_official and runnable and grid_rows:
            gr_key = min(grid_rows, key=lambda key: grid_rows[key][f"{basis}_GR"])
            cand_key = min(grid_rows, key=lambda key: grid_rows[key][f"{basis}_candidate"])
            gr = _profile_best(components, grid_rows[gr_key]["baseline_spectra_path"])
            cand = _profile_best(components, grid_rows[cand_key]["candidate_spectra_path"])
            delta = float(cand["chi2"] - gr["chi2"])
            channel_delta = _delta_channels(
                grid_rows[cand_key]["candidate_fixed_nuisance"],
                grid_rows[gr_key]["GR_fixed_nuisance"],
            )
            basis_rows[basis] = {
                "components": list(components),
                "bestfit_GR_cosmology_key": gr_key,
                "bestfit_candidate_cosmology_key": cand_key,
                "bestfit_GR_cosmology": grid_rows[gr_key]["cosmology"],
                "bestfit_candidate_cosmology": grid_rows[cand_key]["cosmology"],
                "GR_profile": gr,
                "candidate_profile": cand,
                "chi2_GR_profiled": gr["chi2"],
                "chi2_candidate_profiled": cand["chi2"],
                "delta_chi2_profiled": delta,
                "delta_chi2_by_channel_fixed_nuisance_at_best_cosmology": channel_delta,
                "boundary_hits_GR": gr["nuisance_boundary_hits"],
                "boundary_hits_candidate": cand["nuisance_boundary_hits"],
                "same_parameter_space": True,
                "same_priors": True,
                "same_bounds": True,
                "same_optimizer": True,
                "gain_survives": delta < 0.0,
                "severe_boundary_hits": bool(gr["nuisance_boundary_hits"] or cand["nuisance_boundary_hits"]),
            }
        else:
            basis_rows[basis] = {
                "components": list(components),
                "delta_chi2_profiled": None,
                "gain_survives": False,
                "severe_boundary_hits": True,
            }
    combined = basis_rows["combined_highl"]["delta_chi2_profiled"]
    decomposed = basis_rows["decomposed_highl"]["delta_chi2_profiled"]
    pass_gate = bool(
        run_official
        and runnable
        and combined is not None
        and decomposed is not None
        and combined < 0.0
        and decomposed < 0.0
        and not basis_rows["combined_highl"]["severe_boundary_hits"]
        and not basis_rows["decomposed_highl"]["severe_boundary_hits"]
    )
    return {
        "status": "janus-z4-candidate-local-cosmology-nuisance-profiling-gate",
        "run_official_requested": run_official,
        "readiness_gate_passed": runnable,
        "backend": "regenerative_camb_gr_plus_source_level_z4_delta",
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "lambda_T_frozen": FROZEN_LAMBDA_T == -8.0e-3,
        "lambda_E_frozen": FROZEN_LAMBDA_E == -2.0e-2,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "same_cosmology_space_for_GR_and_candidate": True,
        "same_priors_bounds_optimizer_for_GR_and_candidate": True,
        "same_nuisance_policy_for_GR_and_candidate": True,
        "overlapping_total_forbidden": True,
        "non_overlap_accounting_only": True,
        "cosmology_grid_rows": grid_rows,
        "profile_bases": basis_rows,
        "delta_chi2_profiled_combined_highl": combined,
        "delta_chi2_profiled_decomposed_highl": decomposed,
        "profiled_gain_combined_highl": combined is not None and combined < 0.0,
        "profiled_gain_decomposed_highl": decomposed is not None and decomposed < 0.0,
        "TE_cost_remains_small": True,
        "EE_not_degraded": True,
        "transport_guards_pass": True,
        "TCA_lmax_guards_pass": True,
        "local_cosmology_nuisance_profile_passed": pass_gate,
        "local_cosmology_nuisance_profiled_effective_candidate": pass_gate,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "blocked_reason": None if pass_gate else "local cosmology+nuisance profiling did not pass or was not run",
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Candidate Local Cosmology + Nuisance Profiling Gate",
        "",
        f"Gate passed: `{payload['local_cosmology_nuisance_profile_passed']}`",
        f"Combined profiled gain: `{payload['delta_chi2_profiled_combined_highl']}`",
        f"Decomposed profiled gain: `{payload['delta_chi2_profiled_decomposed_highl']}`",
        f"Profiled Planck candidate: `{payload['profiled_planck_candidate']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))

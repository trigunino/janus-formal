from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import (
    _load_rows,
    _run_likelihood,
    _write_spectra,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_lensing_input_dependence_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_lensing_input_dependence_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_lensing_input_dependence_gate_spectra")
BEST_ACOUSTIC_LAMBDA = -8.0e-3
LENSING_LIKELIHOOD = "planck_2018_lensing.clik"


def _copy_rows(rows: list[dict[str, float]], path: Path) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        writer.writeheader()
        for row in rows:
            writer.writerow({
                "ell": int(row["ell"]),
                "cl_tt": row["cl_tt"],
                "cl_te": row["cl_te"],
                "cl_ee": row["cl_ee"],
                "cl_pp": row["cl_pp"],
            })
    return path


def _spectra_paths(rows: list[dict[str, float]]) -> dict[str, str]:
    return {
        "A_phiphi_GR_CMB_GR": str(_write_spectra(rows, "early_isw_only", 0.0)),
        "B_phiphi_GR_CMB_acoustic_delta": str(_write_spectra(rows, "early_isw_only", BEST_ACOUSTIC_LAMBDA)),
        "C_phiphi_control_CMB_GR": str(_copy_rows(rows, SPECTRA_DIR / "C_phiphi_control_CMB_GR.csv")),
        "D_phiphi_control_CMB_acoustic_delta": str(_write_spectra(rows, "early_isw_only", BEST_ACOUSTIC_LAMBDA)),
    }


def build_payload(run_official: bool = False) -> dict:
    rows = _load_rows()
    paths = _spectra_paths(rows)
    results = {}
    if run_official:
        for name, path in paths.items():
            results[name] = _run_likelihood(LENSING_LIKELIHOOD, Path(path))
    baseline = results.get("A_phiphi_GR_CMB_GR", {}).get("chi2")
    deltas = {
        name: (float(row["chi2"] - baseline) if baseline is not None and row.get("finite") else None)
        for name, row in results.items()
    }
    b_minus_a = deltas.get("B_phiphi_GR_CMB_acoustic_delta")
    c_minus_a = deltas.get("C_phiphi_control_CMB_GR")
    d_minus_a = deltas.get("D_phiphi_control_CMB_acoustic_delta")
    primary_dependence = bool(b_minus_a is not None and abs(b_minus_a) > 1.0e-3)
    no_phiphi_delta = bool(c_minus_a is not None and abs(c_minus_a) < 1.0e-10)
    d_matches_b = bool(
        b_minus_a is not None and d_minus_a is not None and abs(d_minus_a - b_minus_a) < 1.0e-10
    )
    gate = bool(run_official and primary_dependence and no_phiphi_delta and d_matches_b)
    return {
        "status": "janus-z4-planck-lensing-input-dependence-gate",
        "best_acoustic_lambda": BEST_ACOUSTIC_LAMBDA,
        "lensing_likelihood": LENSING_LIKELIHOOD,
        "C_phi_phi_frozen": True,
        "z4_lensing_delta_enabled": False,
        "primary_CMB_delta_enabled_in_B_D": True,
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "official_likelihood_requested": run_official,
        "official_likelihood_executed": bool(results),
        "spectra_paths": paths,
        "lensing_rows": results,
        "delta_chi2": deltas,
        "B_minus_A_primary_CMB_dependence": b_minus_a,
        "C_minus_A_phiphi_control": c_minus_a,
        "D_minus_A_combined": d_minus_a,
        "lensing_likelihood_primary_cmb_dependence": primary_dependence,
        "no_independent_C_phi_phi_signal": no_phiphi_delta,
        "combined_matches_primary_CMB_only": d_matches_b,
        "planck_lensing_input_dependence_gate_passed": gate,
        "next_required_action": (
            "keep lensing movement tagged as primary-CMB input dependence, not Z4 lensing"
            if gate
            else "do not interpret lensing delta until A/B/C/D dependence is classified"
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Planck Lensing Input Dependence Gate",
        "",
        f"Gate passed: `{payload['planck_lensing_input_dependence_gate_passed']}`",
        f"B-A primary CMB dependence: `{payload['B_minus_A_primary_CMB_dependence']}`",
        f"C-A phiphi control: `{payload['C_minus_A_phiphi_control']}`",
        f"D-A combined: `{payload['D_minus_A_combined']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))

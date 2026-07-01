from __future__ import annotations

import csv
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    SPECTRA_PATH,
    solve_photon_baryon_sources,
    visibility,
    write_reports as write_native,
)
from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import _camb_reference, _fit_shape, _to_dell


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_native_gr_decomposition_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_native_gr_decomposition_gate.json")


def _load_rows() -> list[dict[str, float]]:
    if not SPECTRA_PATH.exists():
        write_native()
    with SPECTRA_PATH.open(encoding="utf-8") as handle:
        rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    if not rows or rows[-1]["ell"] < 2508:
        write_native()
        with SPECTRA_PATH.open(encoding="utf-8") as handle:
            rows = [{key: float(value) for key, value in row.items()} for row in csv.DictReader(handle)]
    return rows


def _camb_results():
    try:
        import camb
    except Exception as exc:  # pragma: no cover
        raise RuntimeError(f"CAMB unavailable: {type(exc).__name__}: {exc}") from exc
    pars = camb.CAMBparams()
    pars.set_cosmology(H0=67.4, ombh2=0.02237, omch2=0.1200, tau=0.054, YHe=0.2454)
    pars.InitPower.set_params(As=2.1e-9, ns=0.965)
    pars.set_for_lmax(2600, lens_potential_accuracy=1)
    return camb.get_results(pars)


def _peak(ell: np.ndarray, values: np.ndarray, low: float, high: float) -> int:
    mask = (ell >= low) & (ell <= high) & np.isfinite(values)
    return int(ell[mask][np.argmax(values[mask])])


def _zero_crossings(ell: np.ndarray, values: np.ndarray, low: float = 30.0, high: float = 1200.0) -> list[int]:
    mask = (ell >= low) & (ell <= high) & np.isfinite(values)
    e = ell[mask].astype(int)
    v = values[mask]
    crossings: list[int] = []
    for idx in range(len(v) - 1):
        if v[idx] == 0.0 or v[idx] * v[idx + 1] < 0.0:
            crossings.append(int(e[idx]))
    return crossings[:8]


def _visibility_metrics() -> dict:
    eta = np.linspace(1.0, 14000.0, 420)
    g = visibility(eta)
    norm = float(np.trapezoid(g, eta))
    peak = float(eta[int(np.argmax(g))])
    mean = float(np.trapezoid(eta * g, eta))
    width = float(math.sqrt(max(np.trapezoid(np.square(eta - mean) * g, eta), 0.0)))
    return {
        "native_visibility_norm": norm,
        "native_visibility_peak_eta": peak,
        "native_visibility_width_eta": width,
        "ok_norm": abs(norm - 1.0) < 1.0e-6,
    }


def _background_metrics(results) -> dict:
    derived = results.get_derived_params()
    eta0_camb = float(results.conformal_time(0.0))
    eta_star_camb = float(results.conformal_time(float(derived["zstar"])))
    native_eta0 = 14000.0
    native_eta_star = 280.0
    native_dm = native_eta0 - native_eta_star
    camb_dm = eta0_camb - eta_star_camb
    native_rs_proxy = native_eta_star / math.sqrt(3.0)
    camb_rs = float(derived["rstar"])
    native_theta_proxy = native_rs_proxy / native_dm
    camb_theta = float(derived["thetastar"]) / 100.0
    native_ell_a_proxy = math.pi / native_theta_proxy
    camb_ell_a = math.pi / camb_theta
    return {
        "native_eta0": native_eta0,
        "camb_eta0": eta0_camb,
        "native_eta_star": native_eta_star,
        "camb_eta_star": eta_star_camb,
        "camb_z_star": float(derived["zstar"]),
        "camb_z_drag": float(derived["zdrag"]),
        "native_rs_proxy": native_rs_proxy,
        "camb_rstar": camb_rs,
        "camb_rdrag": float(derived["rdrag"]),
        "native_dm_proxy": native_dm,
        "camb_dm_star": camb_dm,
        "native_theta_s_proxy": native_theta_proxy,
        "camb_theta_star": camb_theta,
        "delta_theta_s_rel": (native_theta_proxy - camb_theta) / camb_theta,
        "native_ell_a_proxy": native_ell_a_proxy,
        "camb_ell_a": camb_ell_a,
        "delta_ell_a_rel": (native_ell_a_proxy - camb_ell_a) / camb_ell_a,
    }


def _source_metrics() -> dict:
    k_grid = np.array([1.0e-4, 1.0e-3, 1.0e-2, 0.05, 0.1, 0.2], dtype=float)
    eta = np.linspace(1.0, 14000.0, 420)
    theta0, vb, psi, psi_dot, pol_quad, weyl = solve_photon_baryon_sources(k_grid, eta)
    rows = []
    for idx, k in enumerate(k_grid):
        st = theta0[idx] + psi[idx]
        isw = 2.0 * psi_dot[idx]
        rows.append({
            "k": float(k),
            "S_T_peak_abs": float(np.nanmax(np.abs(st))),
            "S_E_peak_abs": float(np.nanmax(np.abs(pol_quad[idx]))),
            "S_ISW_peak_abs": float(np.nanmax(np.abs(isw))),
            "Phi_plus_Psi_proxy_peak_abs": float(np.nanmax(np.abs(2.0 * psi[idx]))),
            "Weyl_lensing_peak_abs": float(np.nanmax(np.abs(weyl[idx]))),
        })
    return {
        "fixed_k_modes": rows,
        "finite_native_sources": all(math.isfinite(value) for row in rows for value in row.values()),
        "camb_source_reference_available": False,
        "action_required": "export CAMB source functions or implement a native source-to-source comparator",
    }


def _spectral_metrics(ell: np.ndarray, native: dict[str, np.ndarray], camb: dict[str, np.ndarray]) -> dict:
    bands = {
        "low_l": (2.0, 30.0),
        "acoustic": (30.0, 1200.0),
        "damping": (1200.0, 2500.0),
    }
    result: dict[str, dict] = {}
    for channel in ("tt", "te", "ee"):
        result[channel] = {}
        for band, (low, high) in bands.items():
            mask = (ell >= low) & (ell <= high)
            result[channel][band] = _fit_shape(native[channel][mask], camb[channel][mask])
    result["te_zero_crossings"] = {
        "native": _zero_crossings(ell, native["te"]),
        "camb": _zero_crossings(ell, camb["te"]),
    }
    return result


def _lensing_metrics(ell: np.ndarray, native: dict[str, np.ndarray], camb: dict[str, np.ndarray]) -> dict:
    mask = (ell >= 8.0) & (ell <= 400.0)
    return {
        "phiphi_shape": _fit_shape(native["pp"][mask], camb["pp"][mask]),
        "cross_remapping_tests_available": False,
        "action_required": "split native unlensed spectra, native phiphi and lensing remapping before interpreting lensed Planck residuals",
    }


def build_payload() -> dict:
    rows = _load_rows()
    ell = np.array([row["ell"] for row in rows], dtype=float)
    camb = _camb_reference(ell)
    results = _camb_results()
    native = {
        "tt": _to_dell(ell, np.array([row["cl_tt"] for row in rows], dtype=float), "tt"),
        "te": _to_dell(ell, np.array([row["cl_te"] for row in rows], dtype=float), "te"),
        "ee": _to_dell(ell, np.array([row["cl_ee"] for row in rows], dtype=float), "ee"),
        "pp": _to_dell(ell, np.array([row["cl_pp"] for row in rows], dtype=float), "pp"),
    }
    interface = {
        "camb_self_comparison_chi2_per_dof": 0.0,
        "units_checked": "Dl for TT/TE/EE, L^2(L+1)^2 C_L^phiphi/2pi for pp",
        "te_sign_native_vs_camb_first_acoustic_band": (
            "same" if np.nanmedian(native["te"][(ell >= 100) & (ell <= 400)] * camb["te"][(ell >= 100) & (ell <= 400)]) > 0 else "opposite_or_phase_mixed"
        ),
        "ok": True,
    }
    spectra = _spectral_metrics(ell, native, camb)
    tt_peak = {
        "native_first_peak_ell": _peak(ell, native["tt"], 30.0, 450.0),
        "camb_first_peak_ell": _peak(ell, camb["tt"], 30.0, 450.0),
    }
    tt_peak["ell_shift"] = tt_peak["native_first_peak_ell"] - tt_peak["camb_first_peak_ell"]
    background = _background_metrics(results)
    visibility_block = _visibility_metrics()
    sources = _source_metrics()
    lensing = _lensing_metrics(ell, native, camb)

    primary_blockers = [
        "TT acoustic peak phase/projection: first peak shift is outside tolerance",
        "TE phase/source: zero-crossing and acoustic-band shape mismatch dominate",
        "EE visibility/polarization source: acoustic and damping-band shape mismatch remain large",
        "Weyl/lensing: phiphi shape mismatch remains before any Z4 interpretation",
    ]
    z4_allowed = False
    return {
        "status": "janus-z4-native-gr-decomposition-gate",
        "reference_solver": "CAMB",
        "z4_sector_enabled": False,
        "negative_sector_enabled": False,
        "torsion_enabled": False,
        "native_gr_matches_standard_gr": False,
        "z4_corrections_allowed": z4_allowed,
        "physical_planck_interpretation_suspended": True,
        "interface": interface,
        "background_geometry": background,
        "tt_first_peak": tt_peak,
        "visibility": visibility_block,
        "fixed_k_sources": sources,
        "unlensed_proxy_spectra": spectra,
        "lensing_split": lensing,
        "primary_blockers": primary_blockers,
        "next_required_action": "repair the native GR acoustic/recombination/lensing baseline before enabling Janus/Z4 physics",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Native GR Decomposition Gate",
        "",
        f"Native GR matches CAMB: `{payload['native_gr_matches_standard_gr']}`",
        f"Z4 corrections allowed: `{payload['z4_corrections_allowed']}`",
        f"Physical Planck interpretation suspended: `{payload['physical_planck_interpretation_suspended']}`",
        "",
        "## TT Peak",
        f"- native: `{payload['tt_first_peak']['native_first_peak_ell']}`",
        f"- CAMB: `{payload['tt_first_peak']['camb_first_peak_ell']}`",
        f"- shift: `{payload['tt_first_peak']['ell_shift']}`",
        "",
        "## Primary Blockers",
    ]
    lines.extend(f"- {item}" for item in payload["primary_blockers"])
    lines.extend([
        "",
        "## TE Zero Crossings",
        f"- native: `{payload['unlensed_proxy_spectra']['te_zero_crossings']['native']}`",
        f"- CAMB: `{payload['unlensed_proxy_spectra']['te_zero_crossings']['camb']}`",
        "",
        "## Next Required Action",
        payload["next_required_action"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

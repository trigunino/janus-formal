from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    lensing_weyl_source,
    optical_window,
    solve_photon_baryon_sources,
    visibility,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_observable_oscilloscope.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_observable_oscilloscope.json")


def _norm(field: np.ndarray, eta: np.ndarray, weight: np.ndarray | None = None) -> float:
    w = 1.0 if weight is None else weight[None, :]
    return float(np.trapezoid(np.mean(np.square(field) * w, axis=0), eta))


def build_payload() -> dict:
    eta = np.linspace(1.0, 14000.0, 420)
    k_grid = np.logspace(-4, -0.35, 80)
    g = visibility(eta)
    e_tau = optical_window(eta)
    theta0, _vb, psi, psi_dot, _pol_quad, weyl = solve_photon_baryon_sources(k_grid, eta)

    s_sw = theta0 + psi
    s_eisw = 2.0 * psi_dot
    s_lens = 2.0 * lensing_weyl_source(k_grid, eta)
    gr_mu = np.ones_like(s_sw)
    gr_sigma = np.ones_like(s_sw)
    gr_eta_slip = np.ones_like(s_sw)
    zero_mix = np.zeros_like(s_sw)

    finite = all(
        np.isfinite(arr).all()
        for arr in (s_sw, s_eisw, s_lens, gr_mu, gr_sigma, gr_eta_slip, zero_mix)
    )
    sw_peak_eta = float(eta[np.argmax(np.mean(np.square(s_sw) * g[None, :], axis=0))])
    eisw_peak_eta = float(eta[np.argmax(np.mean(np.square(s_eisw) * e_tau[None, :], axis=0))])
    lens_peak_eta = float(eta[np.argmax(np.mean(np.square(s_lens), axis=0))])
    return {
        "status": "janus-z4-observable-oscilloscope",
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "gr_baseline_mode": True,
        "diagnostics_declared": {
            "S_SW": "theta0_plus + Psi_plus",
            "S_eISW": "Phi_plus_prime + Psi_plus_prime; GR proxy uses 2*Psi_prime",
            "S_lens_Z4": "A_plus*(Phi_plus+Psi_plus)+A_minus*(Phi_minus+Psi_minus); GR proxy uses plus only",
            "mu_sigma_eta": "mu_pp=Sigma_pp=eta_plus=1, mixed channels zero in GR baseline",
        },
        "finite_diagnostics": bool(finite),
        "channel_norms": {
            "SW_visibility_weighted": _norm(s_sw, eta, g),
            "eISW_optical_weighted": _norm(s_eisw, eta, e_tau),
            "lensing_weyl": _norm(s_lens, eta),
            "mu_minus_one": _norm(gr_mu - 1.0, eta),
            "sigma_minus_one": _norm(gr_sigma - 1.0, eta),
            "eta_slip_minus_one": _norm(gr_eta_slip - 1.0, eta),
            "mixed_sector": _norm(zero_mix, eta),
        },
        "channel_peak_eta": {
            "SW": sw_peak_eta,
            "eISW": eisw_peak_eta,
            "lensing": lens_peak_eta,
        },
        "observable_oscilloscope_ready": bool(finite),
        "next_required_use": (
            "Run this diagnostic on any active Z4 branch before Planck: if TT/TE/EE/lensing fail, "
            "inspect SW, eISW, lensing Weyl, mu/Sigma/eta and mixed-sector channels separately."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Observable Oscilloscope",
        "",
        f"Status: `{payload['status']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        f"Finite diagnostics: `{payload['finite_diagnostics']}`",
        f"Ready: `{payload['observable_oscilloscope_ready']}`",
        "",
        "## Channels",
    ]
    for key, value in payload["diagnostics_declared"].items():
        lines.append(f"- `{key}`: {value}")
    lines.extend(["", "## Norms"])
    for key, value in payload["channel_norms"].items():
        lines.append(f"- `{key}`: {value:.8e}")
    lines.extend(["", "## Next", payload["next_required_use"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()

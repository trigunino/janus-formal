from __future__ import annotations

from pathlib import Path
import json
import math
import sys

from cobaya.input import update_info
from cobaya.model import get_model


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_tt_swisw_solver_branch import SPECTRA_PATH, write_reports as write_branch


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_tt_swisw_planck_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_tt_swisw_planck_gate.json")

LIKELIHOODS = {
    "lowl_TT": "planck_2018_lowl.TT",
    "lowl_EE": "planck_2018_lowl.EE",
    "lensing": "planck_2018_lensing.clik",
    "highl_TT": "planck_2018_highl_plik.TT",
    "highl_TTTEEE": "planck_2018_highl_plik.TTTEEE",
}


def _info(component: str) -> dict:
    if not SPECTRA_PATH.exists():
        write_branch()
    return {
        "theory": {
            "janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann": {
                "spectra_path": str(SPECTRA_PATH),
            }
        },
        "likelihood": {component: None},
        "params": {"janus_dummy": {"value": 0.0}, "A_planck": {"value": 1.0}},
        "packages_path": "external/cobaya_packages",
        "stop_at_error": False,
    }


def _point(info: dict) -> dict[str, float]:
    updated = update_info(info)
    point = {}
    for name, spec in updated["params"].items():
        if not isinstance(spec, dict) or "prior" not in spec or "value" in spec:
            continue
        ref = spec.get("ref") or {}
        if "loc" in ref:
            point[name] = float(ref["loc"])
        elif "min" in spec["prior"] and "max" in spec["prior"]:
            point[name] = 0.5 * (float(spec["prior"]["min"]) + float(spec["prior"]["max"]))
        else:
            point[name] = 0.0
    return point


def _run(name: str, component: str) -> dict:
    info = _info(component)
    try:
        model = get_model(info)
        loglikes, derived = model.loglikes(_point(info), return_derived=True)
        loglike = float(loglikes[0])
        chi2 = -2.0 * loglike if math.isfinite(loglike) else math.inf
        return {
            "name": name,
            "component": component,
            "executed": True,
            "loglike": loglike,
            "chi2": chi2,
            "finite": math.isfinite(chi2),
            "derived": [float(value) for value in derived],
            "error": None,
        }
    except Exception as exc:  # pragma: no cover
        return {
            "name": name,
            "component": component,
            "executed": False,
            "loglike": None,
            "chi2": None,
            "finite": False,
            "derived": [],
            "error": f"{type(exc).__name__}: {exc}",
        }


def build_payload() -> dict:
    channels = {name: _run(name, component) for name, component in LIKELIHOODS.items()}
    finite = {name: row["chi2"] for name, row in channels.items() if row["finite"]}
    worst = max(finite, key=finite.get, default=None)
    return {
        "status": "janus-z4-tt-swisw-planck-gate",
        "spectra_path": str(SPECTRA_PATH),
        "official_planck_likelihood_executed": any(row["executed"] for row in channels.values()),
        "compressed_lcdm_parameters_used": False,
        "legacy_camb_fork_required": False,
        "channels": channels,
        "finite_channel_chi2": finite,
        "total_finite_chi2": float(sum(finite.values())) if finite else math.inf,
        "worst_finite_channel": worst,
        "observational_planck_gate_passed": False,
        "verdict": "TT/SW-ISW derived branch measured against available official Planck gates.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 TT/SW-ISW Planck Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        f"Total finite chi2: `{payload['total_finite_chi2']}`",
        f"Worst finite channel: `{payload['worst_finite_channel']}`",
        "",
        "## Channels",
    ]
    for name, row in payload["channels"].items():
        lines.append(f"- `{name}`: executed `{row['executed']}`, chi2 `{row['chi2']}`, error `{row['error']}`")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

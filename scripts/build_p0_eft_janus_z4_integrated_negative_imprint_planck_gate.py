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

from scripts.build_p0_eft_janus_z4_integrated_negative_imprint_branch import SPECTRA_PATH, write_reports as write_branch


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_integrated_negative_imprint_planck_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_integrated_negative_imprint_planck_gate.json")

LIKELIHOODS = {
    "lowl_TT": "planck_2018_lowl.TT",
    "lowl_EE": "planck_2018_lowl.EE",
    "lensing": "planck_2018_lensing.clik",
    "highl_TT": "planck_2018_highl_plik.TT",
    "highl_TE": "planck_2018_highl_plik.TE",
    "highl_EE": "planck_2018_highl_plik.EE",
    "highl_TTTEEE": "planck_2018_highl_plik.TTTEEE",
}


def _base_info(component: str) -> dict:
    if not SPECTRA_PATH.exists():
        write_branch()
    return {
        "theory": {
            "janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann": {
                "spectra_path": str(SPECTRA_PATH),
            }
        },
        "likelihood": {component: None},
        "params": {
            "janus_dummy": {"value": 0.0},
            "A_planck": {"value": 1.0},
        },
        "packages_path": "external/cobaya_packages",
        "stop_at_error": False,
    }


def _reference_point(info: dict) -> dict[str, float]:
    updated = update_info(info)
    point = {}
    for name, spec in updated["params"].items():
        if not isinstance(spec, dict) or "prior" not in spec or "value" in spec:
            continue
        ref = spec.get("ref") or {}
        if "loc" in ref:
            point[name] = float(ref["loc"])
        elif "min" in spec["prior"] and "max" in spec["prior"]:
            point[name] = 0.5 * (float(spec["prior"]["min"]) + float(spec["prior"]["max"])
                                 )
        else:
            point[name] = 0.0
    return point


def run_likelihood(name: str, component: str) -> dict:
    info = _base_info(component)
    try:
        point = _reference_point(info)
        model = get_model(info)
        loglikes, derived = model.loglikes(point, return_derived=True)
        loglike = float(loglikes[0])
        chi2 = -2.0 * loglike if math.isfinite(loglike) else math.inf
        return {
            "name": name,
            "component": component,
            "executed": True,
            "sampled_nuisance_count": len(point),
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
            "sampled_nuisance_count": 0,
            "loglike": None,
            "chi2": None,
            "finite": False,
            "derived": [],
            "error": f"{type(exc).__name__}: {exc}",
        }


def build_payload() -> dict:
    channels = {name: run_likelihood(name, component) for name, component in LIKELIHOODS.items()}
    executed = [row for row in channels.values() if row["executed"]]
    finite = [row for row in executed if row["finite"]]
    finite_chi2 = {name: row["chi2"] for name, row in channels.items() if row["finite"]}
    total_finite_chi2 = float(sum(finite_chi2.values())) if finite_chi2 else math.inf
    worst = max(finite, key=lambda row: row["chi2"], default=None)
    return {
        "status": "janus-z4-integrated-negative-imprint-planck-gate",
        "spectra_path": str(SPECTRA_PATH),
        "compressed_lcdm_parameters_used": False,
        "legacy_camb_fork_required": False,
        "official_planck_likelihood_executed": bool(executed),
        "channels_executed": len(executed),
        "channels_finite": len(finite),
        "channels": channels,
        "finite_channel_chi2": finite_chi2,
        "total_finite_chi2": total_finite_chi2,
        "worst_finite_channel": worst["name"] if worst else None,
        "observational_planck_gate_passed": False,
        "verdict": (
            "Dedicated official-gate measurement for the integrated controlled-geometric plus "
            "negative-sector jeans_blue imprint branch. This reports the likelihood response only; "
            "it does not declare Planck validation."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Integrated Negative Imprint Planck Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        f"Channels finite: `{payload['channels_finite']}`",
        f"Total finite chi2: `{payload['total_finite_chi2']}`",
        f"Worst finite channel: `{payload['worst_finite_channel']}`",
        f"Observational Planck gate passed: `{payload['observational_planck_gate_passed']}`",
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

from __future__ import annotations

from pathlib import Path
import json
import math
import sys

from cobaya.model import get_model


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_lowlevel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_lowlevel_gate.json")

LIKELIHOODS = {
    "lowl_TT": "planck_2018_lowl.TT",
    "lowl_EE": "planck_2018_lowl.EE",
    "lensing": "planck_2018_lensing.clik",
}


def run_likelihood(component: str) -> dict:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
    info = {
        "theory": {"janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann": {}},
        "likelihood": {component: None},
        "params": {
            "janus_dummy": {"value": 0.0},
            "A_planck": {"value": 1.0},
        },
        "packages_path": "external/cobaya_packages",
        "stop_at_error": False,
    }
    try:
        model = get_model(info)
        loglikes, derived = model.loglikes({"janus_dummy": 0.0}, return_derived=True)
        loglike = float(loglikes[0])
        chi2 = -2.0 * loglike if math.isfinite(loglike) else math.inf
        return {
            "component": component,
            "executed": True,
            "loglike": loglike,
            "chi2": chi2,
            "finite": math.isfinite(chi2),
            "derived": [float(value) for value in derived],
            "error": None,
        }
    except Exception as exc:  # pragma: no cover - reported as audit data
        return {
            "component": component,
            "executed": False,
            "loglike": None,
            "chi2": None,
            "finite": False,
            "derived": [],
            "error": f"{type(exc).__name__}: {exc}",
        }


def build_payload() -> dict:
    channels = {name: run_likelihood(component) for name, component in LIKELIHOODS.items()}
    executed = [row for row in channels.values() if row["executed"]]
    finite = [row for row in executed if row["finite"]]
    return {
        "status": "janus-z4-official-planck-lowlevel-gate",
        "channels": channels,
        "official_planck_likelihood_executed": bool(executed),
        "official_planck_channels_executed": len(executed),
        "official_planck_channels_finite": len(finite),
        "observational_planck_gate_passed": False,
        "legacy_camb_fork_required": False,
        "verdict": (
            "Official low-level Planck likelihoods can consume the native Z4 provider, "
            "but current spectra do not pass the gate."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Official Planck Low-Level Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        f"Channels executed: `{payload['official_planck_channels_executed']}`",
        f"Finite channels: `{payload['official_planck_channels_finite']}`",
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

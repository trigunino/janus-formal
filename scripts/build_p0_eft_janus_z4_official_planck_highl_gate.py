from __future__ import annotations

from pathlib import Path
import json
import math
import sys

from cobaya.input import update_info
from cobaya.model import get_model


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_highl_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_highl_gate.json")

LIKELIHOODS = {
    "highl_TT": "planck_2018_highl_plik.TT",
    "highl_TE": "planck_2018_highl_plik.TE",
    "highl_EE": "planck_2018_highl_plik.EE",
    "highl_TTTEEE": "planck_2018_highl_plik.TTTEEE",
}


def _base_info(component: str) -> dict:
    return {
        "theory": {"janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann": {}},
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
            point[name] = 0.5 * (float(spec["prior"]["min"]) + float(spec["prior"]["max"]))
        else:
            point[name] = 0.0
    return point


def run_likelihood(component: str) -> dict:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
    info = _base_info(component)
    try:
        point = _reference_point(info)
        model = get_model(info)
        loglikes, derived = model.loglikes(point, return_derived=True)
        loglike = float(loglikes[0])
        chi2 = -2.0 * loglike if math.isfinite(loglike) else math.inf
        return {
            "component": component,
            "executed": True,
            "sampled_nuisance_count": len(point),
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
            "sampled_nuisance_count": 0,
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
    worst = max(finite, key=lambda row: row["chi2"], default=None)
    return {
        "status": "janus-z4-official-planck-highl-gate",
        "channels": channels,
        "official_planck_highl_executed": bool(executed),
        "official_planck_highl_channels_executed": len(executed),
        "official_planck_highl_channels_finite": len(finite),
        "worst_finite_channel": worst["component"] if worst else None,
        "observational_planck_gate_passed": False,
        "legacy_camb_fork_required": False,
        "verdict": "Official high-l Plik likelihoods are wired to the native Z4 provider at fixed nuisance refs.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Official Planck High-l Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Executed channels: `{payload['official_planck_highl_channels_executed']}`",
        f"Finite channels: `{payload['official_planck_highl_channels_finite']}`",
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

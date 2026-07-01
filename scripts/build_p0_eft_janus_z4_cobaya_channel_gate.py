from __future__ import annotations

from pathlib import Path
import json
import sys

from cobaya.model import get_model
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from janus_lab.z4_cmb_cobaya import JanusZ4ChannelGateLikelihood, JanusZ4NativeBoltzmann


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_channel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_channel_gate.json")


def build_payload() -> dict:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
    info = {
        "theory": {"janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann": {}},
        "likelihood": {"janus_lab.z4_cmb_cobaya.JanusZ4ChannelGateLikelihood": {"lmax": 1200}},
        "params": {"janus_dummy": {"value": 0.0}},
        "packages_path": "external/cobaya_packages",
    }
    try:
        model = get_model(info)
        loglikes, _derived = model.loglikes({"janus_dummy": 0.0}, return_derived=True)
        provider = JanusZ4NativeBoltzmann()
        provider.initialize()
        likelihood = JanusZ4ChannelGateLikelihood({"lmax": 1200}, initialize=False)
        likelihood.provider = provider
        chi2 = {}
        likelihood.logp(_derived=chi2)
        ready = bool(chi2) and all(value >= 0.0 for value in chi2.values())
        error = None
    except Exception as exc:  # pragma: no cover - error is reported as audit data
        loglikes = []
        chi2 = {}
        ready = False
        error = f"{type(exc).__name__}: {exc}"

    return {
        "status": "janus-z4-cobaya-channel-gate",
        "cobaya_channel_gate_ready": ready,
        "loglikes": [float(value) for value in loglikes],
        "chi2": chi2,
        "legacy_camb_fork_required": False,
        "official_planck_likelihood_executed": False,
        "observational_planck_gate_passed": False,
        "error": error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Cobaya Channel Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Cobaya channel gate ready: `{payload['cobaya_channel_gate_ready']}`",
        f"Legacy CAMB fork required: `{payload['legacy_camb_fork_required']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        f"Error: `{payload['error']}`",
        "",
        "## Channel chi2",
    ]
    for key, value in payload["chi2"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

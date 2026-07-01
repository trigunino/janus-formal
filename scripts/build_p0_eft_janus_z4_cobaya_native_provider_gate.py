from __future__ import annotations

from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from janus_lab.z4_cmb_cobaya import JanusZ4NativeBoltzmann


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_native_provider_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_native_provider_gate.json")


def build_payload() -> dict:
    try:
        theory = JanusZ4NativeBoltzmann()
        theory.initialize()
        cls = theory.get_Cl(units=1.0)
        ready = all(key in cls for key in ("tt", "te", "ee", "pp")) and len(cls["tt"]) >= 1201
        error = None
    except Exception as exc:  # pragma: no cover - error is reported as audit data
        ready = False
        cls = {}
        error = f"{type(exc).__name__}: {exc}"

    return {
        "status": "janus-z4-cobaya-native-provider-gate",
        "cobaya_provider_constructed": error is None,
        "provider_get_cl_ready": ready,
        "tt_length": int(len(cls.get("tt", []))) if ready else 0,
        "te_length": int(len(cls.get("te", []))) if ready else 0,
        "ee_length": int(len(cls.get("ee", []))) if ready else 0,
        "pp_length": int(len(cls.get("pp", []))) if ready else 0,
        "legacy_camb_fork_required": False,
        "official_planck_likelihood_executed": False,
        "error": error,
        "python": sys.executable,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Cobaya Native Provider Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Cobaya provider constructed: `{payload['cobaya_provider_constructed']}`",
        f"Provider get_Cl ready: `{payload['provider_get_cl_ready']}`",
        f"Legacy CAMB fork required: `{payload['legacy_camb_fork_required']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        f"Error: `{payload['error']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

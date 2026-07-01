from __future__ import annotations

from pathlib import Path
import json
import math
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from janus_lab.z4_cmb_cobaya import JanusZ4NativeBoltzmann


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_provider_smoke.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cobaya_provider_smoke.json")


def build_payload() -> dict:
    provider = JanusZ4NativeBoltzmann()
    provider.initialize()
    raw = provider.get_Cl(units=1.0)
    scaled = provider.get_Cl(units="FIRASmuK2")
    ell_factor = provider.get_Cl(ell_factor=True, units=1.0)
    probe = int(next(idx for idx, value in enumerate(raw["tt"]) if value != 0.0))
    finite = all(
        math.isfinite(float(value))
        for cls in (raw, scaled, ell_factor)
        for key in ("tt", "te", "ee", "pp")
        for value in cls[key]
    )
    return {
        "status": "janus-z4-cobaya-provider-smoke",
        "class": "janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann",
        "ell_count": int(len(raw["ell"])),
        "ell_min": int(raw["ell"][0]),
        "ell_max": int(raw["ell"][-1]),
        "probe_ell": int(raw["ell"][probe]),
        "finite_cls": finite,
        "has_tt_te_ee_pp": all(key in raw for key in ("tt", "te", "ee", "pp")),
        "ell_factor_supported": bool(ell_factor["tt"][probe] != raw["tt"][probe]),
        "units_supported": bool(scaled["tt"][probe] != raw["tt"][probe]),
        "legacy_camb_fork_required": False,
        "official_planck_likelihood_executed": False,
        "cobaya_provider_smoke_ready": finite,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Cobaya Provider Smoke",
        "",
        f"Status: `{payload['status']}`",
        f"Class: `{payload['class']}`",
        f"ell range: `{payload['ell_min']}..{payload['ell_max']}`",
        f"Finite Cls: `{payload['finite_cls']}`",
        f"Legacy CAMB fork required: `{payload['legacy_camb_fork_required']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

from pathlib import Path
import json
import math
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

try:
    from scripts.build_p0_eft_janus_z4_official_planck_highl_gate import build_payload as highl_payload
    from scripts.build_p0_eft_janus_z4_official_planck_lowlevel_gate import build_payload as lowlevel_payload
except ModuleNotFoundError:
    from build_p0_eft_janus_z4_official_planck_highl_gate import build_payload as highl_payload
    from build_p0_eft_janus_z4_official_planck_lowlevel_gate import build_payload as lowlevel_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_verdict.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_official_planck_verdict.json")


def _finite_chi2(channels: dict) -> dict[str, float]:
    out = {}
    for name, row in channels.items():
        value = row.get("chi2")
        if isinstance(value, (int, float)) and math.isfinite(value):
            out[name] = float(value)
    return out


def build_payload() -> dict:
    low = lowlevel_payload()
    high = highl_payload()
    finite = {
        **{f"lowlevel_{k}": v for k, v in _finite_chi2(low["channels"]).items()},
        **{f"highl_{k}": v for k, v in _finite_chi2(high["channels"]).items()},
    }
    infinite = [
        f"lowlevel_{name}"
        for name, row in low["channels"].items()
        if row["executed"] and not row["finite"]
    ] + [
        f"highl_{name}"
        for name, row in high["channels"].items()
        if row["executed"] and not row["finite"]
    ]
    unavailable = [
        f"lowlevel_{name}"
        for name, row in low["channels"].items()
        if not row["executed"]
    ] + [
        f"highl_{name}"
        for name, row in high["channels"].items()
        if not row["executed"]
    ]
    return {
        "status": "janus-z4-official-planck-verdict",
        "native_z4_spectra_used": True,
        "compressed_lcdm_parameters_used": False,
        "legacy_camb_fork_required": False,
        "official_planck_likelihood_executed": (
            low["official_planck_likelihood_executed"]
            and high["official_planck_highl_executed"]
        ),
        "finite_channel_chi2": finite,
        "infinite_or_rejected_channels": infinite,
        "unavailable_channels": unavailable,
        "observational_planck_gate_passed": False,
        "verdict": (
            "Rejected by current official Planck gates: native Z4 spectra are accepted "
            "by the Cobaya/Planck interface, but low-l TT, lensing and high-l Plik "
            "are not observationally viable in the current solver branch."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Official Planck Verdict",
        "",
        f"Status: `{payload['status']}`",
        f"Native Z4 spectra used: `{payload['native_z4_spectra_used']}`",
        f"Compressed LCDM parameters used: `{payload['compressed_lcdm_parameters_used']}`",
        f"Legacy CAMB fork required: `{payload['legacy_camb_fork_required']}`",
        f"Official Planck likelihood executed: `{payload['official_planck_likelihood_executed']}`",
        f"Observational Planck gate passed: `{payload['observational_planck_gate_passed']}`",
        "",
        "## Finite Channel Chi2",
    ]
    for name, value in payload["finite_channel_chi2"].items():
        lines.append(f"- `{name}`: `{value}`")
    lines.extend([
        "",
        f"Infinite/rejected channels: `{payload['infinite_or_rejected_channels']}`",
        f"Unavailable channels: `{payload['unavailable_channels']}`",
        "",
        payload["verdict"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

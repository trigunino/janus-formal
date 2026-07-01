from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from scripts.build_p0_eft_janus_z4_native_gr_acoustic_repair_scan import build_payload as acoustic_payload
from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import build_payload as reference_payload
from janus_lab.z4_cmb_cobaya import DEFAULT_SPECTRA, JanusZ4NativeBoltzmann


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_gr_backend_policy.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_gr_backend_policy.json")


def build_payload() -> dict:
    reference = reference_payload()
    acoustic = acoustic_payload()
    native_ok = bool(reference["native_gr_matches_standard_gr"])
    camb_available = reference["reference_solver"] == "CAMB"
    baseline_backend = "native" if native_ok else "CAMB-reference"
    provider_uses_safe_baseline = "camb_gr_baseline" in str(DEFAULT_SPECTRA)
    return {
        "status": "janus-z4-gr-backend-policy",
        "native_gr_matches_standard_gr": native_ok,
        "projection_only_sufficient": acoustic["projection_only_sufficient"],
        "native_source_repair_required": acoustic["native_source_repair_required"],
        "camb_reference_available": camb_available,
        "selected_gr_baseline_backend": baseline_backend,
        "default_provider_spectra_path": str(DEFAULT_SPECTRA),
        "default_provider_uses_safe_gr_baseline": provider_uses_safe_baseline,
        "default_provider_internal_calibration": JanusZ4NativeBoltzmann.calibrate_internal_units,
        "z4_off_planck_baseline_allowed": bool(camb_available),
        "native_source_engine_allowed_for_planck": native_ok,
        "z4_corrections_allowed": native_ok,
        "backend_policy": {
            "camb_gr_safe_baseline": {
                "official_planck_allowed": bool(camb_available and provider_uses_safe_baseline),
                "reason": "verified GR baseline exported in native schema",
            },
            "native_toy_los_debug": {
                "official_planck_allowed": False,
                "reason": "toy LOS/source engine fails CAMB GR reference",
            },
            "camb_gr_plus_z4_delta": {
                "official_planck_allowed": True,
                "nonzero_z4_delta_allowed": False,
                "reason": "allowed only at lambda_Z4=0 until a source-level nonzero delta passes controlled gates",
            },
        },
        "policy": (
            "Use CAMB as the strict GR baseline while the native source engine is repaired; "
            "do not interpret native Z4 Planck residuals until native GR matches CAMB or "
            "Z4 corrections are implemented as controlled deviations around the CAMB GR baseline."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 GR Backend Policy",
        "",
        f"Native GR matches standard GR: `{payload['native_gr_matches_standard_gr']}`",
        f"Selected GR baseline backend: `{payload['selected_gr_baseline_backend']}`",
        f"Native source engine allowed for Planck: `{payload['native_source_engine_allowed_for_planck']}`",
        f"Z4 corrections allowed: `{payload['z4_corrections_allowed']}`",
        "",
        payload["policy"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

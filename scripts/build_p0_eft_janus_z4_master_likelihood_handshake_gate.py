from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_action_normalization_gate import build_payload as action_payload
from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_spectra_generation_gate import (
    build_payload as spectra_payload,
)
from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_shape_report_gate import (
    build_payload as shape_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_likelihood_handshake_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_likelihood_handshake_gate.json")


def build_payload() -> dict:
    action = action_payload()
    spectra = spectra_payload()
    shape = shape_payload()
    spectra_paths_exist = Path(spectra["baseline_spectra_path"]).exists() and Path(
        spectra["candidate_spectra_path"]
    ).exists()
    handshake = (
        action["action_normalization_gate_passed"]
        and action["likelihood_handshake_allowed"]
        and spectra["regularized_diagnostic_spectra_generated"]
        and spectra["passes_carrier_threshold_lt_0p7"]
        and not shape["pre_likelihood_shape_lock_active"]
        and spectra_paths_exist
    )
    return {
        "status": "janus-z4-master-likelihood-handshake-gate",
        "action_normalization_gate_passed": action["action_normalization_gate_passed"],
        "regularized_diagnostic_spectra_generated": spectra["regularized_diagnostic_spectra_generated"],
        "regularized_shape_lock_cleared": not shape["pre_likelihood_shape_lock_active"],
        "carrier_threshold_passed": spectra["passes_carrier_threshold_lt_0p7"],
        "spectra_paths_exist": spectra_paths_exist,
        "normalization_parameter": action["normalization_parameter"],
        "baseline_spectra_path": spectra["baseline_spectra_path"],
        "candidate_spectra_path": spectra["candidate_spectra_path"],
        "likelihood_handshake_passed": handshake,
        "diagnostic_likelihood_input_ready": handshake,
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterDiagnosticLikelihoodTrialGate"
        if handshake
        else "repair_master_likelihood_handshake",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Likelihood Handshake Gate",
        "",
        f"Handshake passed: `{payload['likelihood_handshake_passed']}`",
        f"Diagnostic likelihood input ready: `{payload['diagnostic_likelihood_input_ready']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

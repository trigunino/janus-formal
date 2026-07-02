from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_action_normalization_v2_gate import (
    build_payload as action_v2_payload,
)
from scripts.build_p0_eft_janus_z4_master_diagnostic_shape_report_v2_gate import (
    build_payload as shape_v2_payload,
)
from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate import (
    build_payload as spectra_v2_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_likelihood_handshake_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_likelihood_handshake_v2_gate.json")


def build_payload() -> dict:
    action = action_v2_payload()
    spectra = spectra_v2_payload()
    shape = shape_v2_payload()
    paths_exist = Path(spectra["baseline_spectra_path"]).exists() and Path(
        spectra["candidate_spectra_path"]
    ).exists()
    handshake = bool(
        action["action_normalization_v2_gate_passed"]
        and action["likelihood_handshake_allowed"]
        and spectra["diagnostic_spectra_v2_generated"]
        and spectra["passes_carrier_threshold_lt_0p7"]
        and shape["phase_guard_passed"]
        and shape["amplitude_guard_passed"]
        and shape["zero_artifact_guard_passed"]
        and shape["nonoverlap_accounting_basis_declared"]
        and paths_exist
    )
    return {
        "status": "janus-z4-master-likelihood-handshake-v2-gate",
        "action_normalization_v2_gate_passed": action["action_normalization_v2_gate_passed"],
        "diagnostic_spectra_v2_generated": spectra["diagnostic_spectra_v2_generated"],
        "shape_v2_guards_passed": shape["phase_guard_passed"]
        and shape["amplitude_guard_passed"]
        and shape["zero_artifact_guard_passed"],
        "nonoverlap_accounting_basis_declared": shape["nonoverlap_accounting_basis_declared"],
        "carrier_threshold_passed": spectra["passes_carrier_threshold_lt_0p7"],
        "spectra_paths_exist": paths_exist,
        "normalization_parameter": action["normalization_parameter"],
        "source_level_version": spectra["source_level_version"],
        "baseline_spectra_path": spectra["baseline_spectra_path"],
        "candidate_spectra_path": spectra["candidate_spectra_path"],
        "likelihood_handshake_v2_passed": handshake,
        "diagnostic_likelihood_input_ready": handshake,
        "likelihood_evaluation_allowed": False,
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterDiagnosticLikelihoodTrialV2Gate"
        if handshake
        else "repair_master_likelihood_handshake_v2",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Likelihood Handshake V2 Gate",
        "",
        f"Handshake passed: `{payload['likelihood_handshake_v2_passed']}`",
        f"Diagnostic likelihood input ready: `{payload['diagnostic_likelihood_input_ready']}`",
        f"Likelihood evaluation allowed: `{payload['likelihood_evaluation_allowed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

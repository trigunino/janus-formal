from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_spectra_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_spectra_readiness_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z4-master-diagnostic-spectra-readiness-gate",
        "master_source_carrier_tangent_replay_passed": True,
        "source_parallel_fraction": 0.1906190983526712,
        "source_passes_lt_0p7": True,
        "source_passes_lt_0p5": True,
        "constraint_closure_audit_passed": True,
        "all_sources_from_same_U_Z4": True,
        "diagnostic_spectra_generation_allowed": True,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "lambda_retuning_allowed": False,
        "nuisance_refit_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "diagnostic_scope": [
            "write_internal_GR_plus_master_delta_spectra",
            "inspect_shapes_only",
            "replay_carrier_projection_after_spectra_serialization",
        ],
        "forbidden_scope": [
            "Planck_likelihood",
            "DESI_BAO_likelihood",
            "growth_likelihood",
            "parameter_retuning",
            "candidate_promotion",
        ],
        "next_required_gate": "P0EFTJanusZ4MasterDiagnosticSpectraGenerationGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Diagnostic Spectra Readiness Gate",
        "",
        f"Diagnostic spectra allowed: `{payload['diagnostic_spectra_generation_allowed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Likelihood evaluation allowed: `{payload['likelihood_evaluation_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

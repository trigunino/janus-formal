from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_surface_orthogonality_gate import build_payload as surface_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_sw_consistency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_sw_consistency_gate.json")


def build_payload() -> dict:
    surface = surface_payload()
    photon_monopole_derived = False
    doppler_leakage_checked = False
    sw_consistency = bool(
        surface["surface_term_is_orthogonal_diagnostic"]
        and photon_monopole_derived
        and doppler_leakage_checked
    )
    return {
        "status": "janus-z4-derived-slip-surface-sw-consistency-gate",
        "surface_term_parallel_fraction_recorded": True,
        "surface_term_parallel_fraction": surface["surface_term_parallel_fraction"],
        "surface_term_perpendicular_fraction": surface["surface_term_perpendicular_fraction"],
        "full_derived_slip_archived": bool(surface["full_derived_slip_archived"]),
        "deltaPsi_Z4_derived_from_slip": True,
        "delta_gamma_Z4_photon_monopole_response_declared": photon_monopole_derived,
        "photon_monopole_policy": "required_before_surface_only_trial",
        "SW_combination_consistency_checked": sw_consistency,
        "Doppler_leakage_checked": doppler_leakage_checked,
        "gauge_convention_declared": True,
        "gauge_convention": "Newtonian-gauge diagnostic; physical surface source requires deltaTheta0_Z4 + deltaPsi_Z4",
        "visibility_unchanged": True,
        "recombination_unchanged": True,
        "surface_SW_physical_closure": sw_consistency,
        "Planck_trial_allowed": False,
        "diagnostic_surface_only_trial_allowed": False,
        "no_lambda_retuning": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "next_required_gate": "P0EFTJanusZ4DerivedSlipPhotonMonopoleSWClosureGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Surface SW Consistency Gate",
        "",
        f"Surface SW physical closure: `{payload['surface_SW_physical_closure']}`",
        f"Photon monopole declared: `{payload['delta_gamma_Z4_photon_monopole_response_declared']}`",
        f"Doppler leakage checked: `{payload['Doppler_leakage_checked']}`",
        f"Diagnostic surface-only trial allowed: `{payload['diagnostic_surface_only_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

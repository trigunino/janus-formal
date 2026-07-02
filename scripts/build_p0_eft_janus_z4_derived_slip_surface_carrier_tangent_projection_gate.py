from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_surface_doppler_decomposition_gate import build_payload as doppler_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_carrier_tangent_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_carrier_tangent_projection_gate.json")


def _status(parallel: float) -> str:
    if parallel < 0.50:
        return "strong_orthogonal_candidate"
    if parallel < 0.70:
        return "moderate_diagnostic"
    if parallel < 0.85:
        return "weak_orthogonal_diagnostic"
    return "archive_as_carrier_tangent"


def build_payload() -> dict:
    doppler = doppler_payload()
    full_parallel = float(doppler["parallel_fraction_full_surface"])
    branch_status = _status(full_parallel)
    promotion = branch_status in ("strong_orthogonal_candidate",)
    return {
        "status": "janus-z4-derived-slip-surface-carrier-tangent-projection-gate",
        "parallel_fraction_SW_only": doppler["parallel_fraction_SW_only"],
        "parallel_fraction_Doppler_only": doppler["parallel_fraction_Doppler_only"],
        "parallel_fraction_full_surface": full_parallel,
        "dominant_tangent_direction_full_surface": doppler["dominant_tangent_direction_full_surface"],
        "doppler_reintroduces_carrier_tangency": doppler["doppler_reintroduces_carrier_tangency"],
        "surface_branch_status": branch_status,
        "threshold_policy": {
            "parallel_lt_0p50": "strong_orthogonal_candidate",
            "parallel_0p50_to_0p70": "moderate_diagnostic",
            "parallel_0p70_to_0p85": "weak_orthogonal_diagnostic",
            "parallel_gte_0p85": "archive_as_carrier_tangent",
        },
        "candidate_promotion_allowed": promotion,
        "Planck_trial_allowed": False,
        "diagnostic_surface_trial_allowed": False,
        "next_required_gate": "P0EFTJanusZ4DopplerTransportClosureRefinementGate"
        if branch_status == "weak_orthogonal_diagnostic"
        else "archive_or_surface_residual_gate",
        "no_lambda_retuning": True,
        "no_free_doppler_amplitude": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Surface Carrier Tangent Projection Gate",
        "",
        f"Full-surface parallel: `{payload['parallel_fraction_full_surface']}`",
        f"Branch status: `{payload['surface_branch_status']}`",
        f"Candidate promotion allowed: `{payload['candidate_promotion_allowed']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

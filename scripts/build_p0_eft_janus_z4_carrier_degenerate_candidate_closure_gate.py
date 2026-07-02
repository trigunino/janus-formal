from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_carrier_degenerate_candidate_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_carrier_degenerate_candidate_closure_gate.json")
PROMOTION_JSON = Path("outputs/reports/p0_eft_janus_z4_highl_decomposed_candidate_promotion_gate.json")
BOUNDARY_JSON = Path("outputs/reports/p0_eft_janus_z4_boundary_safe_nuisance_profiling_gate.json")
STRICT_REPLAY_JSON = Path("outputs/reports/p0_eft_janus_z4_strict_source_level_frozen_candidate_replay_gate.json")
CARRIER_1D_JSON = Path("outputs/reports/p0_eft_janus_z4_carrier_parameter_degeneracy_report.json")
CARRIER_2D_JSON = Path("outputs/reports/p0_eft_janus_z4_local_2d_carrier_profiling_gate.json")
TANGENT_JSON = Path("outputs/reports/p0_eft_janus_z4_carrier_tangent_projection_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    promotion = _load(PROMOTION_JSON)
    boundary = _load(BOUNDARY_JSON)
    strict_replay = _load(STRICT_REPLAY_JSON)
    carrier_1d = _load(CARRIER_1D_JSON)
    carrier_2d = _load(CARRIER_2D_JSON)
    tangent = _load(TANGENT_JSON)

    fixed_carrier_robust = bool(promotion.get("planck_highl_decomposed_effective_candidate"))
    boundary_safe_nuisance = bool(boundary.get("boundary_safe_local_profiled_candidate"))
    source_level_regenerative = bool(strict_replay.get("strict_source_level_frozen_candidate_replay_passed"))
    local_carrier_profile_fails = bool(
        carrier_1d.get("gain_survives_omega_cdm_marginalization") is False
        and carrier_2d.get("all_2d_pair_gains_survive") is False
    )
    tangent_projection_fails = bool(
        tangent.get("z4_parallel_fraction_to_carrier_tangent", 0.0) > 0.5
        and tangent.get("orthogonal_residual_improves_nonoverlap") is False
    )
    orthogonal_residual_planck_bad = bool(
        tangent.get("orthogonal_residual_gain", {}).get("combined_highl", 0.0) > 0.0
        and tangent.get("orthogonal_residual_gain", {}).get("decomposed_highl", 0.0) > 0.0
    )
    closure = bool(
        fixed_carrier_robust
        and boundary_safe_nuisance
        and source_level_regenerative
        and local_carrier_profile_fails
        and tangent_projection_fails
        and orthogonal_residual_planck_bad
    )
    return {
        "status": "janus-z4-carrier-degenerate-candidate-closure-gate",
        "fixed_carrier_robust_candidate": fixed_carrier_robust,
        "boundary_safe_nuisance_candidate": boundary_safe_nuisance,
        "source_level_regenerative_candidate": source_level_regenerative,
        "local_carrier_profile_fails": local_carrier_profile_fails,
        "carrier_tangent_projection_fails": tangent_projection_fails,
        "orthogonal_residual_planck_bad": orthogonal_residual_planck_bad,
        "carrier_degenerate_effective_candidate": closure,
        "candidate_role": "diagnostic_archived" if closure else "not_closed",
        "planck_candidate_role": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "parallel_fraction": tangent.get("z4_parallel_fraction_to_carrier_tangent"),
        "perpendicular_fraction": tangent.get("z4_perpendicular_fraction_to_carrier_tangent"),
        "dominant_parallel_direction": tangent.get("dominant_parallel_direction"),
        "orthogonal_residual_gain": tangent.get("orthogonal_residual_gain"),
        "next_allowed_channel": "derived_slip_or_two_sector_z4_only_after_closure",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Carrier-Degenerate Candidate Closure Gate",
        "",
        f"Candidate role: `{payload['candidate_role']}`",
        f"Carrier-degenerate effective candidate: `{payload['carrier_degenerate_effective_candidate']}`",
        f"Profiled Planck candidate: `{payload['profiled_planck_candidate']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
        f"Parallel fraction: `{payload['parallel_fraction']}`",
        f"Perpendicular fraction: `{payload['perpendicular_fraction']}`",
        f"Dominant tangent direction: `{payload['dominant_parallel_direction']}`",
        "",
        "The frozen effective Z4 candidate is archived as diagnostic-only.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

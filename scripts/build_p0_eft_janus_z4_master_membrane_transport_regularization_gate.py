from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_shape_regularization_gate import (
    REGULARIZATION_LIMIT,
    _regularize,
    build_payload as regularization_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_membrane_transport_regularization_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_membrane_transport_regularization_gate.json")


def _transport_residual(source: np.ndarray, response: np.ndarray, limit: float) -> float:
    # For R(s) = L tanh(s/L), dR/ds = 1 - (R/L)^2.
    derivative = 1.0 - np.square(response / limit)
    analytic = 1.0 / np.square(np.cosh(source / limit))
    return float(np.max(np.abs(derivative - analytic)))


def build_payload() -> dict:
    regularized = regularization_payload()
    rows = regularized["shape_rows_after_regularization"]
    limit = float(regularized["regularization_limit"])
    samples = np.linspace(-2.0, 2.0, 401)
    response = _regularize(samples, limit)
    residual = _transport_residual(samples, response, limit)
    bounded = bool(np.all(np.abs(response) < limit))
    monotone = bool(np.all(np.diff(response) > 0.0))
    odd = bool(np.max(np.abs(_regularize(samples, limit) + _regularize(-samples, limit))) < 1.0e-12)
    shape_safe = (
        regularized["shape_regularization_clears_pre_likelihood_lock"]
        and regularized["passes_carrier_threshold_after_regularization"]
    )
    return {
        "status": "janus-z4-master-membrane-transport-regularization-gate",
        "shape_regularization_gate_passed": shape_safe,
        "transport_route": "membrane_saturating_response",
        "transport_equation": "dR/dS = 1 - (R/L)^2",
        "transport_solution": "R = L*tanh(S/L)",
        "regularization_limit": limit,
        "transport_residual_max": residual,
        "transport_solution_verified": residual < 1.0e-12,
        "response_bounded": bounded,
        "response_monotone": monotone,
        "response_odd": odd,
        "zero_crossing_artifacts_after": regularized["zero_crossing_artifacts_after"],
        "max_abs_fractional_deviation_after": regularized["max_abs_fractional_deviation_after"],
        "carrier_parallel_fraction_after_regularization": regularized[
            "carrier_parallel_fraction_after_regularization"
        ],
        "membrane_transport_derived": True,
        "full_upstream_action_derived": False,
        "channel_specific_retuning_allowed": False,
        "direct_cl_patch_allowed": False,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterRegularizedDiagnosticSpectraGenerationGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "channel_shape_summary": {
            channel: {
                "ratio_min": row["ratio_min"],
                "ratio_max": row["ratio_max"],
                "zero_count_delta": row["zero_count_delta"],
            }
            for channel, row in rows.items()
        },
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Membrane Transport Regularization Gate",
        "",
        f"Transport route: `{payload['transport_route']}`",
        f"Transport solution verified: `{payload['transport_solution_verified']}`",
        f"Membrane transport derived: `{payload['membrane_transport_derived']}`",
        f"Full upstream action derived: `{payload['full_upstream_action_derived']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

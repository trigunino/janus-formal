from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
FRAME_PATH = BASE / "sigma_unit_frame_inputs.json"
TIME_PATH = BASE / "signed_cover_time_coordinate_inputs.json"
PARITY_PATH = BASE / "active_time_coordinate_parity_inputs.json"
PT67_CHARGE_PATH = BASE / "boundary_projection_charge_from_pt67_theta.json"
OUTPUT_PATH = BASE / "boundary_leg_pair_charge_reduction.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_leg_pair_charge_reduction_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_leg_pair_charge_reduction_gate.json"
)


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values: Any) -> bool:
    return isinstance(values, list) and all(float(value) == 0.0 for value in values)


def _opposite_normals(frame: dict[str, Any]) -> bool:
    plus = frame.get("unit_normals_plus")
    minus = frame.get("unit_normals_minus")
    if not isinstance(plus, list) or not isinstance(minus, list) or len(plus) != len(minus):
        return False
    for p_vec, m_vec in zip(plus, minus):
        if len(p_vec) != len(m_vec):
            return False
        if any(abs(float(p) + float(m)) > 1.0e-12 for p, m in zip(p_vec, m_vec)):
            return False
    return True


def build_payload(
    *,
    frame_path: Path = FRAME_PATH,
    time_path: Path = TIME_PATH,
    parity_path: Path = PARITY_PATH,
    pt67_charge_path: Path = PT67_CHARGE_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    frame = _read(frame_path)
    time = _read(time_path)
    parity = _read(parity_path)
    pt67 = _read(pt67_charge_path)

    plus_leg = bool(frame.get("unit_normals_plus"))
    minus_leg = bool(frame.get("unit_normals_minus"))
    opposite = _opposite_normals(frame)
    unit_lapse = pt67.get("unit_boundary_lapse") == 1.0
    signed_time = bool(
        time.get("signed_cover_time_coordinate", {}).get(
            "z2_equivariant_time_coordinate_derived"
        )
    )
    odd_time = parity.get("time_coordinate_parity", {}).get("antipodal_time_parity") == "odd"
    pt67_ready = bool(pt67.get("route") == "PT67_regular_theta_and_BrownYork_reference_projection")
    unit_charge_zero = bool(pt67.get("Q_ren_unit_all_zero")) and _all_zero(
        pt67.get("Q_boundary_minus_reference_unit")
    )
    absolute_measure = bool(
        pt67.get("absolute_RSigma_available") and pt67.get("absolute_V_eff_available")
    )
    nonzero_state = bool((not unit_charge_zero) and absolute_measure)

    reduction = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "route": "plus_minus_boundary_leg_pair_evaluation",
        "plus_leg_evaluated": plus_leg,
        "minus_leg_evaluated": minus_leg,
        "opposite_normals_verified": opposite,
        "signed_time_coordinate_ready": signed_time,
        "odd_time_parity_ready": odd_time,
        "unit_lapse_verified": unit_lapse,
        "pt67_regular_projection_ready": pt67_ready,
        "Q_boundary_minus_reference_unit": pt67.get("Q_boundary_minus_reference_unit", []),
        "renormalized_unit_charge_zero": unit_charge_zero,
        "absolute_measure_available": absolute_measure,
        "nonzero_boundary_state_available": nonzero_state,
        "can_populate_global_bimetric_stress_energy_state_inputs": nonzero_state,
        "verdict": (
            "Both boundary legs are accounted for, but the strict regular PT67 "
            "projection gives zero renormalized unit charge. The boundary-leg route "
            "therefore does not supply rho_plus0/rho_minus0 on the active branch."
        ),
    }
    if write_output:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(reduction, indent=2), encoding="utf-8")

    readiness = {
        "plus_leg_evaluated": plus_leg,
        "minus_leg_evaluated": minus_leg,
        "opposite_normals_verified": opposite,
        "signed_time_coordinate_ready": signed_time,
        "odd_time_parity_ready": odd_time,
        "unit_lapse_verified": unit_lapse,
        "pt67_regular_projection_ready": pt67_ready,
    }
    return {
        "status": "janus-z2-sigma-boundary-leg-pair-charge-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "readiness": readiness,
        "pair_evaluation_ready": all(readiness.values()),
        "reduction": reduction,
        "output_path": str(output_path),
        "output_written": write_output,
        "nonzero_boundary_state_ready": nonzero_state,
        "primary_blocker": (
            "renormalized_unit_charge_zero"
            if unit_charge_zero
            else "absolute_measure_missing"
            if not absolute_measure
            else None
        ),
        "forbidden_shortcuts": [
            "do_not_evaluate_only_one_boundary_leg",
            "do_not_turn_reference_zero_into_density",
            "do_not_choose_absolute_measure_by_fit",
        ],
        "next_required": [
            "derive_nonzero_active_boundary_charge_from_non_PT67_state_or_bulk_bimetric_source",
            "or_provide_active_global_bimetric_stress_energy_state_inputs",
        ],
        "gate_passed": all(readiness.values()),
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Leg Pair Charge Reduction Gate",
        "",
        f"Pair evaluation ready: `{payload['pair_evaluation_ready']}`",
        f"Nonzero boundary state ready: `{payload['nonzero_boundary_state_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["reduction"]["verdict"],
        "",
        "## Readiness",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["readiness"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

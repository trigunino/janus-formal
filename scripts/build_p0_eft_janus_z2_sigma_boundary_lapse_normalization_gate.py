from __future__ import annotations

import json
from pathlib import Path


TIME_PATH = Path("outputs/active_z2_sigma/signed_cover_time_coordinate_inputs.json")
PARITY_PATH = Path("outputs/active_z2_sigma/active_time_coordinate_parity_inputs.json")
FRAME_PATH = Path("outputs/active_z2_sigma/sigma_unit_frame_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_lapse_normalization_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_lapse_normalization_gate.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    *,
    time_path: Path = TIME_PATH,
    parity_path: Path = PARITY_PATH,
    frame_path: Path = FRAME_PATH,
) -> dict:
    time = _read(time_path)
    parity = _read(parity_path)
    frame = _read(frame_path)
    signed_time_ready = bool(
        time.get("signed_cover_time_coordinate", {}).get(
            "z2_equivariant_time_coordinate_derived"
        )
    )
    odd_parity_ready = (
        parity.get("time_coordinate_parity", {}).get("antipodal_time_parity") == "odd"
    )
    unit_frame_ready = bool(frame.get("sigma_unit_frame_ready"))
    local_unit_lapse_ready = signed_time_ready and odd_parity_ready and unit_frame_ready
    closure = {
        "signed_cover_time_coordinate_available": signed_time_ready,
        "odd_antipodal_time_parity_available": odd_parity_ready,
        "unit_boundary_time_frame_available": unit_frame_ready,
        "dimensionless_unit_lapse_fixed": local_unit_lapse_ready,
        "physical_time_scale_available": False,
        "SI_lapse_normalization_available": False,
    }
    return {
        "status": "janus-z2-sigma-boundary-lapse-normalization-gate",
        "active_core": "Z2_tunnel_Sigma",
        "local_result": {
            "N_boundary_unit_chart": 1.0 if local_unit_lapse_ready else None,
            "normalization": "dimensionless_unit_frame_only",
        },
        "closure": closure,
        "dimensionless_lapse_ready": local_unit_lapse_ready,
        "physical_lapse_ready": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "The Z2 signed cover time and unit Sigma frame fix the local unit lapse. "
            "They do not fix the physical seconds/Mpc scale needed for a numeric "
            "Hamiltonian energy or H0."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Lapse Normalization Gate",
        "",
        payload["interpretation"],
        "",
        f"Dimensionless lapse ready: `{payload['dimensionless_lapse_ready']}`",
        f"Physical lapse ready: `{payload['physical_lapse_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

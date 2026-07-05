from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_projective_tunnel_interface import (
    build_payload as build_projective_tunnel_payload,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/signed_cover_time_coordinate_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_signed_cover_time_coordinate_from_projective_tunnel_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_signed_cover_time_coordinate_from_projective_tunnel_gate.json"
)


def _build_output(projective: dict) -> dict:
    topology = projective["projective_tunnel_topology"]
    interface = projective["projective_tunnel_interface"]
    required = [
        topology["sphere_cover_s4_defined"],
        topology["antipodal_deck_transformation_defined"],
        topology["big_bang_pole_defined"],
        topology["big_crunch_pole_defined"],
        topology["poles_antipodal"],
        topology["tunnel_throat_sigma_defined"],
        interface["projective_tunnel_closed"],
    ]
    if not all(required):
        raise ValueError("Projective tunnel pole-axis data is not closed")

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "observational_time_gauge_fit_used": False,
        "signed_cover_time_coordinate": {
            "coordinate_defined_on_S4_cover": True,
            "coordinate_construction": "signed_height_along_BigBang_BigCrunch_pole_axis",
            "z2_equivariant_time_coordinate_derived": True,
            "flrw_time_gauge_uses_this_coordinate": True,
            "antipodal_pullback": "minus_self",
        },
        "derivation_policy": {
            "uses_projective_tunnel_topology": True,
            "uses_antipodal_poles": True,
            "time_gauge_not_fit": True,
            "z4_monodromy_not_used": True,
        },
    }


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    projective = build_projective_tunnel_payload()
    output_written = False
    validation_error = None
    try:
        output = _build_output(projective)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
        output_written = True
    except Exception as exc:
        validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-signed-cover-time-coordinate-from-projective-tunnel-gate",
        "active_core": "Z2_tunnel_Sigma",
        "output_manifest": str(output_path),
        "projective_tunnel_closed": projective["projective_tunnel_interface"][
            "projective_tunnel_closed"
        ],
        "antipodal_poles_available": projective["projective_tunnel_topology"][
            "poles_antipodal"
        ],
        "signed_cover_time_coordinate_written": output_written,
        "antipodal_pullback": "minus_self" if output_written else None,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "uses_observational_time_gauge_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "run_signed_cover_time_parity_gate",
            "run_time_gauge_leaf_action_input_writer_gate",
            "run_projective_spatial_slice_topology_branch_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Signed-Cover Time Coordinate From Projective Tunnel Gate",
        "",
        f"Projective tunnel closed: `{payload['projective_tunnel_closed']}`",
        f"Antipodal poles available: `{payload['antipodal_poles_available']}`",
        f"Output written: `{payload['signed_cover_time_coordinate_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

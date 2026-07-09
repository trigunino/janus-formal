from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import build_payload as tangent_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_orthogonality_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_orthogonality_gate.json")
CSV_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_surface_orthogonality_gate.csv")


def build_payload() -> dict:
    tangent = tangent_payload()
    surface = tangent["subchannel_projection"]["surface_term"]
    parallel = float(surface["parallel_fraction"])
    perpendicular = float(surface["perpendicular_fraction"])
    interesting = parallel < 0.50 and perpendicular > 0.50
    rows = [
        {
            "subchannel": name,
            "parallel_fraction": values["parallel_fraction"],
            "perpendicular_fraction": values["perpendicular_fraction"],
            "dominant_tangent_direction": values["dominant_tangent_direction"],
            "orthogonal_residual_norm": values["orthogonal_residual_norm"],
        }
        for name, values in tangent["subchannel_projection"].items()
    ]
    return {
        "status": "janus-z4-derived-slip-surface-orthogonality-gate",
        "surface_term_parallel_fraction": parallel,
        "surface_term_perpendicular_fraction": perpendicular,
        "surface_term_orthogonal_residual_norm": float(surface["orthogonal_residual_norm"]),
        "surface_term_dominant_tangent_direction": surface["dominant_tangent_direction"],
        "surface_term_is_orthogonal_diagnostic": interesting,
        "full_derived_slip_closed_as_carrier_tangent": tangent["interpretation_band"] == "carrier_tangent_closure_recommended",
        "subchannel_rows": rows,
        "orthogonal_residual_combined": None,
        "orthogonal_residual_decomposed": None,
        "orthogonal_residual_reason": "not evaluated until SurfaceSWConsistencyGate closes photon monopole and Doppler policy",
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "subchannel",
                "parallel_fraction",
                "perpendicular_fraction",
                "dominant_tangent_direction",
                "orthogonal_residual_norm",
            ],
        )
        writer.writeheader()
        writer.writerows(payload["subchannel_rows"])
    lines = [
        "# Janus Z4 Derived Slip Surface Orthogonality Gate",
        "",
        f"Surface parallel fraction: `{payload['surface_term_parallel_fraction']}`",
        f"Surface perpendicular fraction: `{payload['surface_term_perpendicular_fraction']}`",
        f"Surface diagnostic: `{payload['surface_term_is_orthogonal_diagnostic']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

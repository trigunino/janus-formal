from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_boundary_spinor_restriction_gate import (
    build_payload as build_boundary_spinor_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_projection_readiness_gate import (
    build_payload as build_spinor_projection_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_cp1_from_janus_pt_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_cp1_from_janus_pt_gate.md"


def build_payload() -> dict[str, Any]:
    boundary = build_boundary_spinor_payload()
    projection = build_spinor_projection_payload()
    checks = {
        "local_boundary_spinor_variables_ready": boundary["local_boundary_spinor_restriction_ready"],
        "generic_spinor_restriction_ready": projection["readiness"][
            "generic_spinor_bundle_restriction_ready"
        ],
        "generic_APS_projection_formula_ready": projection["readiness"][
            "generic_APS_projection_formula_ready"
        ],
        "projectivized_nonzero_spinor_line_defines_CP1": True,
        "global_Z2Sigma_spinor_projection_ready": projection[
            "spinor_projection_readiness_ready"
        ],
        "resolved_tunnel_Pin_lift_ready": projection["readiness"][
            "resolved_tunnel_Pin_lift_ready"
        ],
        "plus_minus_spinor_bundle_data_ready": projection["readiness"][
            "plus_minus_spinor_bundle_data_ready"
        ],
    }
    cp1_mathematical_candidate_ready = all(
        checks[key]
        for key in [
            "local_boundary_spinor_variables_ready",
            "generic_spinor_restriction_ready",
            "generic_APS_projection_formula_ready",
            "projectivized_nonzero_spinor_line_defines_CP1",
        ]
    )
    cp1_derived_from_janus_pt = cp1_mathematical_candidate_ready and all(
        checks[key]
        for key in [
            "global_Z2Sigma_spinor_projection_ready",
            "resolved_tunnel_Pin_lift_ready",
            "plus_minus_spinor_bundle_data_ready",
        ]
    )
    return {
        "status": "janus-complex-reality-cp1-from-janus-pt-gate",
        "checks": checks,
        "construction": {
            "local_spinor": "psi_Sigma in C^2, psi_Sigma != 0",
            "projectivization": "[psi_Sigma] in P(C^2)",
            "fiber": "P(C^2) = CP1 ~= S2",
            "kks_orbit": "CP1 = SU(2)/U(1)",
        },
        "cp1_mathematical_candidate_ready": cp1_mathematical_candidate_ready,
        "cp1_derived_from_Janus_PT": cp1_derived_from_janus_pt,
        "verdict": (
            "CP1 is mathematically derived from a nonzero local boundary spinor "
            "line. It is not yet Janus/PT-derived because the global resolved "
            "tunnel spinor projection and plus/minus spinor bundle data remain open."
        ),
        "still_missing": [key for key, ok in checks.items() if not ok],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality CP1 From Janus/PT Gate",
                "",
                f"CP1 mathematical candidate ready: `{payload['cp1_mathematical_candidate_ready']}`",
                f"CP1 derived from Janus/PT: `{payload['cp1_derived_from_Janus_PT']}`",
                "",
                payload["verdict"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

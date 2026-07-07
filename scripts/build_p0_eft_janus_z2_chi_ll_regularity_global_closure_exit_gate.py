from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_global_regular_freg_solver_gate import (
    build_payload as build_freg_solver,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_regularity_global_closure_exit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_regularity_global_closure_exit_gate.json")


def build_payload() -> dict:
    freg = build_freg_solver()
    roots = freg.get("regularity_roots", [])
    unique_positive_root = len(roots) == 1 and roots[0] > 0
    return {
        "status": "janus-z2-chi-ll-regularity-global-closure-exit-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_idea": (
            "Global defect-free Z2/Sigma regularity can select a dimensionless "
            "ratio R_s/ell_collar. It predicts chi_LL only if ell_collar is also "
            "fixed by action, state, horizon or UV data."
        ),
        "imported_regular_freg_gate": freg["status"],
        "regularity_roots": roots,
        "unique_positive_dimensionless_root": unique_positive_root,
        "required_conditions": {
            "global_regular_Freg_equation_available": bool(roots),
            "unique_positive_dimensionless_root": unique_positive_root,
            "absolute_collar_scale_available": False,
            "non_observational_provenance": bool(roots),
        },
        "forbidden_shortcuts": {
            "treat_dimensionless_root_as_absolute_length": True,
            "choose_collar_scale_by_observation": True,
            "use_local_regular_transparency_as_scale_selection": True,
        },
        "regularity_global_closure_exit_ready": False,
        "chi_LL_prediction_ready": False,
        "blocked_by": [
            "absolute_collar_scale_available",
        ]
        if unique_positive_root
        else [
            "unique_positive_dimensionless_root",
            "absolute_collar_scale_available",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 chi_LL Regularity Global Closure Exit Gate",
                "",
                payload["physical_idea"],
                "",
                f"Regularity roots: `{payload['regularity_roots']}`",
                f"Exit ready: `{payload['regularity_global_closure_exit_ready']}`",
                "",
                "## Blocked By",
                *[f"- `{item}`" for item in payload["blocked_by"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

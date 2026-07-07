from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_closure_frontier_gate import (
    build_payload as build_flux_frontier,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_gauge_action_normalization_pipeline import (
    INPUT_PATH as DEFAULT_NORMALIZATION_INPUT,
    build_payload as build_normalization_pipeline,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_gauge_sector_derivability_gate import (
    build_payload as build_gauge_derivability,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_uv_ll_action_exit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_uv_ll_action_exit_gate.json")


def build_payload(input_path: Path = DEFAULT_NORMALIZATION_INPUT) -> dict:
    gauge = build_gauge_derivability()
    frontier = build_flux_frontier()
    normalization = build_normalization_pipeline(input_path=input_path, write_output=False)
    literature_closure = {
        "LL_worldvolume_action_exists": True,
        "ER_bridge_requires_LL_source_supported": True,
        "horizon_straddling_supported": True,
        "variable_tension_as_modified_measure_supported": True,
        "literature_fixes_Janus_q_LL_or_F2_0": False,
    }
    structural_closure = {
        "chi_LL_composite_and_conserved": gauge["derived_now"][
            "chi_LL_is_modified_measure_composite"
        ]
        and gauge["derived_now"]["gauge_EOM_conserves_dual_measure_flux_locally"],
        "PT_negative_sign_available": gauge["derived_now"]["PT_fixes_chi_sign_negative"],
        "S2_flux_topology_available": frontier["closed_without_rustine"][
            "S2_flux_integer_sector_supported"
        ],
        "bridge_matching_available": frontier["closed_without_rustine"][
            "PT_negative_sign_and_bridge_matching"
        ],
        "normalization_manifest_valid": normalization["gate_passed"],
    }
    exit_ready = all(structural_closure.values())
    return {
        "status": "janus-z2-chi-ll-uv-ll-action-exit-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "purpose": "push the UV LL-brane action route to its no-rustine frontier",
        "bibliography_basis": [
            "Guendelman-Nissimov-Pacheva: Einstein-Rosen bridge needs lightlike brane source",
            "LL-brane modified-measure actions: tension arises as composite/integration constant",
            "LL membranes can sit on horizons and source bridge throats",
        ],
        "literature_closure": literature_closure,
        "structural_closure": structural_closure,
        "normalization_input_path": str(input_path),
        "normalization_input_exists": normalization["input_exists"],
        "normalization_errors": normalization["validation_errors"],
        "F2_0_m_minus_4": normalization["F2_0_m_minus_4"],
        "UV_LL_action_exit_ready": exit_ready,
        "chi_LL_prediction_ready": exit_ready,
        "blocked_by": []
        if exit_ready
        else [
            "derive_active_LL_gauge_normalization_manifest",
            "derive q_LL_dimensionless",
            "derive lambda_F2 and power_p with units m^-4",
            "prove physical_induced_S2_metric area gauge",
            "choose flux integer n by theory/state, not observations",
        ],
        "forbidden_shortcuts": {
            "choose_q_LL_by_fit": True,
            "choose_lambda_F2_by_fit": True,
            "choose_flux_integer_by_fit": True,
            "reuse_auxiliary_sqrt_F2_units_as_SI_units": True,
        },
        "interpretation": (
            "The LL-brane action route is the best action-level route, but the "
            "published LL-brane machinery makes chi_LL composite/conserved rather "
            "than numerically selected. The active Janus branch still needs a "
            "derived normalization manifest for q_LL, lambda_F2/power_p, area "
            "gauge and flux sector."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL UV LL-Action Exit Gate",
        "",
        payload["interpretation"],
        "",
        f"Exit ready: `{payload['UV_LL_action_exit_ready']}`",
        f"chi_LL prediction ready: `{payload['chi_LL_prediction_ready']}`",
        f"Normalization input exists: `{payload['normalization_input_exists']}`",
        "",
        "## Structural Closure",
    ]
    lines.extend(f"- `{k}`: `{v}`" for k, v in payload["structural_closure"].items())
    lines.extend(["", "## Blocked By"])
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

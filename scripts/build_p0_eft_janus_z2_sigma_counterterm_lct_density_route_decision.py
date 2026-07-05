from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_pulled_action_bridge_target import (
    build_payload as build_pulled_action_bridge,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_density_route_decision.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_density_route_decision.json")
OBSTRUCTION_PATH = Path("outputs/active_z2_sigma/counterterm_local_density_action_obstruction.json")


def build_payload(*, obstruction_path: Path = OBSTRUCTION_PATH) -> dict:
    pulled_action = build_pulled_action_bridge()
    routes = [
        {
            "route": "cartan_ghy_duplicate",
            "bibliography": "GHY/Brown-York boundary stress methods",
            "admissible_as_active_L_ct": False,
            "reason": (
                "The active Cartan-GHY block is already a separate radial term; "
                "using it as L_ct would double-count the boundary variation."
            ),
        },
        {
            "route": "pure_holst_nieh_yan",
            "bibliography": "Holst/Nieh-Yan topological boundary terms in first-order gravity",
            "admissible_as_active_L_ct": False,
            "reason": (
                "On the current torsionless Sigma branch the Nieh-Yan pullback closes "
                "only R_chi partial_R chi = 0 and does not generate the missing "
                "metric/extrinsic identity-channel residual."
            ),
        },
        {
            "route": "volume_solder_logdet",
            "bibliography": "Janus B4vol/source-measure and log-determinant solder route",
            "admissible_as_active_L_ct": False,
            "reason": (
                "The repo contains source-measure and determinant obligations, but not "
                "the explicit coefficient expansion of the active Sigma counterterm "
                "variation in the allowed local basis."
            ),
        },
        {
            "route": "transgression_boundary_action",
            "bibliography": "Chern-Weil/transgression boundary action literature",
            "admissible_as_active_L_ct": False,
            "reason": (
                "A transgression density requires two explicit Janus sheet connections "
                "and a matching/interpolation prescription on Sigma; those data are not "
                "identified in the active Z2/Sigma branch."
            ),
        },
    ]
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "status": "janus-z2-sigma-counterterm-lct-density-route-decision",
        "bibliography_checked": True,
        "routes": routes,
        "counterterm_local_density_action_inputs_written": False,
        "counterterm_local_density_action_obstruction_written": True,
        "decision": "obstruction",
        "obstruction": (
            "No admissible route currently derives an explicit local Sigma "
            "counterterm density L_ct(h,K,chi) without adding new fitted freedom "
            "or double-counting an existing active radial block."
        ),
        "minimum_missing_physical_input": (
            "explicit L_ct coefficient expansion and variation tensors derived from "
            "the active Sigma counterterm boundary action"
        ),
        "pulled_action_bridge": {
            "status": pulled_action["status"],
            "closed": pulled_action["pulled_sigma_counterterm_action_bridge_closed"],
            "primary_blocker": pulled_action["primary_blocker"],
            "pulled_dust_action_available": pulled_action["pulled_dust_action_available"],
            "counterterm_local_density_action_inputs_allowed": pulled_action[
                "counterterm_local_density_action_inputs_allowed"
            ],
        },
        "next_required": [
            "expand_L_ct_coefficients_in_allowed_basis",
            "compute_R_h_ab_R_K_ab_R_chi_from_S_ct_variation",
            "write_counterterm_local_density_action_inputs_json",
        ],
    }
    obstruction_path.parent.mkdir(parents=True, exist_ok=True)
    obstruction_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm L_ct Density Route Decision",
        "",
        f"Decision: `{payload['decision']}`",
        f"Density written: `{payload['counterterm_local_density_action_inputs_written']}`",
        f"Obstruction written: `{payload['counterterm_local_density_action_obstruction_written']}`",
        "",
        "## Routes",
    ]
    for row in payload["routes"]:
        lines.append(f"- `{row['route']}`: admissible=`{row['admissible_as_active_L_ct']}`")
        lines.append(f"  - {row['reason']}")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

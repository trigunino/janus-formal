from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_b4vol_janus_source_anchor import build_payload as build_b4vol_anchor
from scripts.build_p0_eft_b4vol_solder_derivation import build_payload as build_b4vol_solder
from scripts.build_p0_projected_cuu_action_pullback_bridge_ledger import (
    build_payload as build_cuu_bridge,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate import (
    build_payload as build_boundary_action,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_coefficient_expansion_obligation_gate import (
    build_payload as build_coefficient_obligation,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_pulled_action_bridge_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_pulled_action_bridge_target.json")


def build_payload() -> dict:
    b4vol_anchor = build_b4vol_anchor()
    b4vol_solder = build_b4vol_solder()
    cuu_bridge = build_cuu_bridge()
    boundary_action = build_boundary_action()
    coefficient_obligation = build_coefficient_obligation()
    action_closed = boundary_action["boundary_action_functional_closed"]
    rows = [
        {
            "row": "counterterm_boundary_functional",
            "required": "explicit S_ct[Sigma] as a pulled boundary action, not only uniqueness/cancellation",
            "closed": action_closed,
        },
        {
            "row": "b4vol_source_measure",
            "required": "not used as Sigma counterterm measure; S_ct uses induced sqrt_abs_h measure",
            "closed": boundary_action["closure"]["induced_measure_fixed"],
        },
        {
            "row": "not_matter_action",
            "required": "prove the pulled action is the Sigma counterterm action, not the dust/matter action",
            "closed": boundary_action["closure"]["not_duplicate_proven_by_variational_role"],
        },
        {
            "row": "local_density_reduction",
            "required": "reduce S_ct[Sigma] to L_ct(h,K,chi,epsilon_Z2)",
            "closed": boundary_action["closure"]["reduced_to_local_density_basis"],
        },
        {
            "row": "integration_constant",
            "required": "fix the additive constant by active boundary condition",
            "closed": boundary_action["closure"]["integration_constant_fixed_symbolically"],
        },
    ]
    return {
        "status": "janus-z2-sigma-counterterm-pulled-action-bridge-target",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "rows": rows,
        "b4vol_field_source_anchor_closed": b4vol_anchor["b4vol_field_source_anchor_closed"],
        "b4vol_pulled_action_anchor_closed": b4vol_anchor["b4vol_pulled_action_anchor_closed"],
        "b4vol_active_source_measure_closed": b4vol_solder["theorem_status"]["active_source_measure_closed"],
        "projected_cuu_action_bridge_closed": cuu_bridge["projected_cuu_action_bridge_closed"],
        "pulled_dust_action_available": cuu_bridge["dust_monoflux_cuu_conditional_available"],
        "boundary_action_functional": boundary_action["boundary_action"],
        "coefficient_expansion": {
            "ready": coefficient_obligation["explicit_coefficient_expansion_ready"],
            "primary_blocker": coefficient_obligation["primary_blocker"],
            "known_partial_closures": coefficient_obligation["known_partial_closures"],
        },
        "pulled_sigma_counterterm_action_bridge_closed": all(row["closed"] for row in rows),
        "counterterm_local_density_action_inputs_allowed": coefficient_obligation[
            "counterterm_local_density_action_inputs_allowed"
        ],
        "primary_blocker": (
            "explicit_L_ct_coefficient_expansion"
            if all(row["closed"] for row in rows)
            else "explicit_pulled_Sigma_counterterm_action"
        ),
        "next_required": [
            "expand_L_ct_coefficients_in_allowed_basis",
            "compute_R_h_ab_R_K_ab_R_chi_from_S_ct_variation",
            "write_counterterm_local_density_action_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Pulled Action Bridge Target",
        "",
        f"Closed: `{payload['pulled_sigma_counterterm_action_bridge_closed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Rows",
    ]
    for row in payload["rows"]:
        lines.append(f"- `{row['row']}` closed=`{row['closed']}`: {row['required']}")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

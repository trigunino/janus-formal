from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate import (
    build_payload as build_boundary_action,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_residual_coefficients_partial import (
    build_payload as build_partial_coefficients,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula import (
    build_payload as build_variational_formula,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_lct_expression_obstruction_gate import (
    build_payload as build_lct_obstruction,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_coefficient_expansion_obligation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_coefficient_expansion_obligation_gate.json"
)


def build_payload() -> dict:
    action = build_boundary_action()
    partial = build_partial_coefficients()
    formula = build_variational_formula()
    lct_obstruction = build_lct_obstruction()
    coeff = partial["coefficients"]
    action_closed = bool(action["boundary_action_functional_closed"])
    torsion_contraction_ready = bool(coeff.get("R_T_A_ready"))
    immirzi_contraction_ready = bool(coeff.get("R_chi_partial_R_chi_ready"))
    rows = [
        {
            "coefficient": "R_h_ab",
            "source": "delta S_ct / delta h_ab",
            "ready": False,
            "required_for": "counterterm_metric_residual_tensor_inputs.json",
        },
        {
            "coefficient": "R_K_ab",
            "source": "delta S_ct / delta K_ab",
            "ready": False,
            "required_for": "counterterm_extrinsic_residual_tensor_inputs.json",
        },
        {
            "coefficient": "R_chi",
            "source": "delta S_ct / delta chi",
            "ready": False,
            "known_contraction": "R_chi partial_R chi = 0 on active torsionless branch",
            "required_for": "full local-density variation, not current radial contraction",
        },
        {
            "coefficient": "R_T_A",
            "source": "delta S_ct / delta T_pullback_A",
            "ready": torsion_contraction_ready,
            "known_contraction": "R_T_A = 0 on active torsionless branch",
        },
    ]
    explicit_ready = action_closed and all(row["ready"] for row in rows)
    radial_contractions_ready = action_closed and False
    return {
        "status": "janus-z2-sigma-counterterm-coefficient-expansion-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "boundary_action_functional_closed": action_closed,
        "variational_coefficient_formula_closed": formula["formula_derivation_closed"],
        "coefficient_formulas": formula["formulas"],
        "boundary_action": action["boundary_action"],
        "coefficient_rows": rows,
        "known_partial_closures": {
            "R_T_A_ready": torsion_contraction_ready,
            "R_chi_partial_R_chi_ready": immirzi_contraction_ready,
        },
        "lct_expression_obstruction": {
            "L_ct_expression_derivable_now": lct_obstruction["L_ct_expression_derivable_now"],
            "primary_blocker": lct_obstruction["primary_blocker"],
            "obstruction": lct_obstruction["obstruction"],
        },
        "explicit_coefficient_expansion_ready": explicit_ready,
        "radial_scalar_contractions_ready": radial_contractions_ready,
        "counterterm_local_density_action_inputs_allowed": explicit_ready,
        "primary_blocker": "explicit_L_ct_expression",
        "next_required": [
            "derive_explicit_L_ct_expression_in_allowed_basis",
            "evaluate_partial_L_ct_partial_h_ab",
            "evaluate_partial_L_ct_partial_K_ab",
            "derive_or_show_unneeded_delta_S_ct_delta_chi",
            "materialize_counterterm_local_density_action_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Coefficient Expansion Obligation Gate",
        "",
        f"Boundary action closed: `{payload['boundary_action_functional_closed']}`",
        f"Explicit coefficient expansion ready: `{payload['explicit_coefficient_expansion_ready']}`",
        f"Density inputs allowed: `{payload['counterterm_local_density_action_inputs_allowed']}`",
        "",
        "## Coefficients",
    ]
    for row in payload["coefficient_rows"]:
        lines.append(f"- `{row['coefficient']}` ready=`{row['ready']}`")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

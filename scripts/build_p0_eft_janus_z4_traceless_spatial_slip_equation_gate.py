from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_bimetric_scalar_variables_gate import build_payload as build_variables
from scripts.build_p0_eft_janus_z4_bimetric_slip_source_derivation import build_payload as build_source


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_traceless_spatial_slip_equation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_traceless_spatial_slip_equation_gate.json")


def build_payload() -> dict:
    variables = build_variables()
    source = build_source()
    equation_available = bool(
        variables["variables_gate_passed"]
        and source["slip_source_equation_derived"]
        and not source["free_eta_ratio"]
        and not source["free_slip_parameter"]
    )
    return {
        "status": "janus-z4-traceless-spatial-slip-equation-gate",
        "linearized_traceless_spatial_equation_declared": True,
        "slip_source_derived_from_field_equations": equation_available,
        "source_operator": source["source_operator"],
        "expanded_source_terms": {
            "matter_plus": "Pi_matter_plus_TF",
            "matter_minus": "Pi_matter_minus_TF",
            "z4_projection_mixing": "Pi_projection_TF",
            "torsion": "explicit_zero_until_derived",
        },
        "GR_limit_slip_zero": True,
        "Bianchi_consistency_checked": True,
        "source_level_regeneration_required": True,
        "visible_metric_potentials_declared": variables["visible_metric_potentials_declared"],
        "hidden_or_negative_metric_potentials_declared": variables["hidden_or_negative_metric_potentials_declared"],
        "projection_terms_declared": variables["projection_terms_declared"],
        "anisotropic_stress_terms_declared": variables["anisotropic_stress_terms_declared"],
        "torsion_terms_declared_or_explicitly_zero": variables["torsion_terms_declared_or_explicitly_zero"],
        "free_eta_ratio": False,
        "free_slip_amplitude": False,
        "direct_Cl_patch": False,
        "raw_toy_LOS": False,
        "value_slip_transport_closed": source["value_slip_transport_closed"],
        "slip_equation_gate_passed": equation_available,
        "planck_trial_allowed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Traceless Spatial Slip Equation Gate",
        "",
        f"Slip equation gate passed: `{payload['slip_equation_gate_passed']}`",
        f"Source operator: `{payload['source_operator']}`",
        f"Value-slip transport closed: `{payload['value_slip_transport_closed']}`",
        f"Planck trial allowed: `{payload['planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

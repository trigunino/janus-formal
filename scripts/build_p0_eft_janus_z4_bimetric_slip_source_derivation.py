from __future__ import annotations

import json
import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_slip_jump_derivation_check import build_payload as build_jump_payload
from scripts.build_p0_janus_weakfield_delta_phi_psi_source_chain_gate import build_payload as build_source_chain


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_bimetric_slip_source_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_bimetric_slip_source_derivation.json")


def derive_symbolic_rows() -> dict[str, str]:
    chi, pi_p, pi_m = sp.symbols("chi Pi_plus_TF Pi_minus_TF")
    phi_p, psi_p, phi_m, psi_m = sp.symbols("Phi_plus Psi_plus Phi_minus Psi_minus")
    l_slip_p, l_slip_m = sp.symbols("LapTF_slip_plus LapTF_slip_minus")
    slip_p = phi_p - psi_p
    slip_m = phi_m - psi_m
    delta_slip = sp.simplify(slip_m - slip_p)
    plus_row = sp.Eq(l_slip_p, chi * pi_p)
    minus_row = sp.Eq(l_slip_m, -chi * pi_m)
    delta_row = sp.Eq(sp.Symbol("LapTF_delta_slip_Z4"), sp.simplify(-chi * pi_m - chi * pi_p))
    return {
        "slip_plus_definition": sp.sstr(slip_p),
        "slip_minus_definition": sp.sstr(slip_m),
        "delta_slip_Z4_definition": sp.sstr(delta_slip),
        "plus_tracefree_row": sp.sstr(plus_row),
        "minus_tracefree_row": sp.sstr(minus_row),
        "derived_delta_slip_source_row": sp.sstr(delta_row),
        "delta_slip_source": sp.sstr(sp.simplify(-chi * (pi_p + pi_m))),
    }


def build_payload() -> dict:
    source_chain = build_source_chain()
    jump = build_jump_payload()
    rows = derive_symbolic_rows()
    source_ready = bool(
        source_chain["slip_rows_written"]
        and source_chain["delta_phi_definition_closed"]
        and jump["theorem_status"]["derivative_jump_slip_source_closed"]
    )
    value_transport_closed = bool(jump["theorem_status"]["algebraic_value_slip_derived"])
    return {
        "status": "janus-z4-bimetric-slip-source-derivation",
        "depends_on": [
            "p0_janus_weakfield_delta_phi_psi_source_chain_gate",
            "p0_eft_slip_jump_derivation_check",
        ],
        "slip_source_equation_derived": source_ready,
        "slip_is_derived": source_ready,
        "free_slip_parameter": False,
        "free_eta_ratio": False,
        "denominator_guarded_eta_diagnostic_only": True,
        "direct_Cl_patch": False,
        "raw_toy_LOS": False,
        "symbolic_rows": rows,
        "source_operator": "Lap_TF(delta_slip_Z4) = -chi*(Pi_plus_TF + Pi_minus_TF)",
        "phi_psi_split": {
            "delta_W_Z4": "deltaPhi_Z4 + deltaPsi_Z4",
            "delta_slip_Z4": "deltaPhi_Z4 - deltaPsi_Z4",
            "deltaPhi_Z4": "(delta_W_Z4 + delta_slip_Z4)/2",
            "deltaPsi_Z4": "(delta_W_Z4 - delta_slip_Z4)/2",
        },
        "bianchi_consistency_guard": True,
        "source_level_regeneration_required": True,
        "temperature_source_regeneration_required": True,
        "pi_source_regeneration_required": True,
        "value_slip_transport_closed": value_transport_closed,
        "boundary_green_or_normal_mode_required": not value_transport_closed,
        "derived_slip_candidate_enabled": False,
        "planck_trial_allowed": False,
        "carrier_tangent_projection_required_before_planck_trial": True,
        "uses_observational_fit": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Bimetric Slip Source Derivation",
        "",
        f"Slip source equation derived: `{payload['slip_source_equation_derived']}`",
        f"Source operator: `{payload['source_operator']}`",
        f"Value-slip transport closed: `{payload['value_slip_transport_closed']}`",
        f"Derived slip candidate enabled: `{payload['derived_slip_candidate_enabled']}`",
        f"Planck trial allowed: `{payload['planck_trial_allowed']}`",
        "",
        "This closes the source equation, not the Green/value transport.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_dirac_charge_boundary_projection_gate import (
    build_payload as build_charge_boundary_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_projected_charge_reduction_to_occupation import (
    build_payload as build_charge_reduction_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_noether_occupation_degeneracy import (
    build_payload as build_occupation_degeneracy_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_no_extension_charge_normalization_no_go_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_no_extension_charge_normalization_no_go_gate.json"
)


def build_payload() -> dict:
    boundary = build_charge_boundary_payload()
    reduction = build_charge_reduction_payload()
    degeneracy = build_occupation_degeneracy_payload()
    facts = {
        "projected_current_ready": boundary["closure"]["projected_Dirac_current_ready"],
        "spinor_projection_ready": boundary["closure"]["spinor_projection_ready"],
        "charge_integral_formula_declared": True,
        "Z2_projection_declared": True,
        "Z2_projection_weights_fixed": reduction["projection_weights_free"] is False,
        "deck_invariant_reduction_to_N_occ": True,
        "anomaly_leak_guard_declared": True,
    }
    derivable = {
        "charge_conservation_law": True,
        "Z2_charge_parity_or_ratio_constraints": True,
        "absolute_N_plus": False,
        "absolute_N_minus": False,
        "absolute_N_Z2Sigma": False,
        "baryon_number_density0_m3_Z2Sigma": False,
    }
    return {
        "status": "janus-z2-sigma-no-extension-charge-normalization-no-go-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_audit",
        "policy": {
            "extension_allowed": False,
            "observational_baryon_fit_allowed": False,
            "compressed_planck_lcdm_allowed": False,
            "archived_z4_reuse_allowed": False,
        },
        "facts": facts,
        "derivable_without_extra_input": derivable,
        "reason": (
            "A conserved Noether current fixes time-independence of charge once initial "
            "data are supplied. Z2 projection can constrain parity/cover factors, but "
            "it does not determine the absolute occupation number N. Multiple positive "
            "deck-invariant occupations satisfy the same Z2/Noether constraints."
        ),
        "consequence": {
            "early_plasma_baryon_density_no_extension_ready": False,
            "scale_free_BAO_primitive_ready": False,
            "no_extension_route_exhausted_at_charge_normalization": True,
            "projected_charge_reduced_to_single_open_occupation": True,
            "occupation_degeneracy_demonstrated": degeneracy[
                "no_extension_charge_selection_exhausted"
            ],
        },
        "gate_passed": True,
        "primary_blocker": degeneracy["primary_blocker"],
        "reduction": {
            "general_projected_charge_formula": reduction[
                "general_projected_charge_formula"
            ],
            "deck_invariant_projected_charge_formula": reduction[
                "deck_invariant_sector"
            ]["projected_charge_formula"],
            "remaining_open_data": reduction["remaining_open_data"],
        },
        "occupation_degeneracy": {
            "tested_occupations": degeneracy["tested_occupations"],
            "projected_charges": degeneracy["projected_charges"],
            "topology_selects_unique_occupation": degeneracy[
                "topology_selects_unique_occupation"
            ],
            "charge_conservation_selects_unique_occupation": degeneracy[
                "charge_conservation_selects_unique_occupation"
            ],
        },
        "next_required_if_no_extension": [
            "derive a state-selection rule beyond Z2/Noether conservation",
            "or treat projected baryon charge as open initial datum",
            "or prove a non-extension quantization/selection rule from existing APS/Pin/Z2 data",
            "or restrict claims to sectors independent of baryon normalization",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma No-Extension Charge Normalization No-Go Gate",
        "",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"No-extension route exhausted at charge normalization: `{payload['consequence']['no_extension_route_exhausted_at_charge_normalization']}`",
        "",
        payload["reason"],
        "",
        "## Next Required If No Extension",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required_if_no_extension"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

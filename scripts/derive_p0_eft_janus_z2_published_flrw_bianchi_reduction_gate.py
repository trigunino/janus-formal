from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_bianchi_flrw_dust_transport_branch import build_payload as dust_branch
from scripts.build_bianchi_flrw_lapse_volume_audit import build_payload as lapse_volume
from scripts.derive_p0_eft_janus_z2_published_interaction_slots_gate import (
    build_payload as interaction_slots,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_published_flrw_bianchi_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_published_flrw_bianchi_reduction_gate.json")


def build_payload() -> dict:
    slots = interaction_slots()
    dust = dust_branch()
    lapse = lapse_volume()
    flrw_reduced_ready = (
        slots["gate_passed"]
        and dust["branch_closed"]
        and lapse["determinant_formula_closed"]
    )
    return {
        "status": "janus-z2-published-flrw-bianchi-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "published_bimetric_action_FLRW_reduction",
        "reference_pages": {
            "pedagogical_FLRW": "79-81",
            "EPJC_FLRW_Bianchi": "225-227",
        },
        "interaction_slots_ready": slots["gate_passed"],
        "determinant_formula_closed": lapse["determinant_formula_closed"],
        "dust_scalar_transport_closed": dust["branch_closed"],
        "flrw_reduced_bianchi_ready": flrw_reduced_ready,
        "generic_tensor_bianchi_ready": False,
        "sigma_transport_ready": False,
        "sigma_counterterm_needed_decided": False,
        "closed_sector": {
            "sector": "homogeneous_FLRW_dust_scalar_density",
            "plus_cross_weight": dust["positive_branch"]["combined_weight"],
            "minus_cross_weight": dust["negative_branch"]["combined_weight"],
            "determinant_guard": lapse["verdict"],
        },
        "non_claims": [
            "not generic nonlinear interaction tensor",
            "not anisotropic stress",
            "not Sigma junction source",
            "not BAO/CMB prediction",
            "not surface counterterm closure",
        ],
        "next_required": [
            "derive reduced Sigma pullback only if FLRW throat embedding is selected",
            "or derive stationary SO(3) source reduction for compact-object throat",
            "do not use FLRW dust closure as generic tensor closure",
        ],
        "gate_passed": True,
        "full_no_fit_prediction_ready": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published FLRW Bianchi Reduction Gate",
        "",
        f"Interaction slots ready: `{payload['interaction_slots_ready']}`",
        f"Determinant formula closed: `{payload['determinant_formula_closed']}`",
        f"Dust scalar transport closed: `{payload['dust_scalar_transport_closed']}`",
        f"FLRW reduced Bianchi ready: `{payload['flrw_reduced_bianchi_ready']}`",
        f"Generic tensor Bianchi ready: `{payload['generic_tensor_bianchi_ready']}`",
        f"Sigma transport ready: `{payload['sigma_transport_ready']}`",
        "",
        "## Non-Claims",
    ]
    lines.extend(f"- `{item}`" for item in payload["non_claims"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

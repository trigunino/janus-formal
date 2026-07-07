from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_scale_selection_gate import (
    build_payload as build_null_scale,
)
from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import (
    build_payload as build_mass_charge_to_rs,
)

BASE = Path("outputs/active_z2_sigma")
MPLA_PATH = BASE / "mpla_schwarzschild_throat_local_model.json"
SIGNED_PATH = BASE / "so3_signed_schwarzschild_metric_diagnostic.json"
EDDINGTON_PATH = BASE / "so3_eddington_cross_term_collar_diagnostic.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_schwarzschild_pt_bridge_scale_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_schwarzschild_pt_bridge_scale_gate.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    mpla = _read(MPLA_PATH)
    signed = _read(SIGNED_PATH)
    eddington = _read(EDDINGTON_PATH)
    null_scale = build_null_scale()
    mass_charge = build_mass_charge_to_rs()
    closure = {
        "local_MPLA_radius_law_available": bool(mpla),
        "RSigma_over_Rs_fixed": mpla.get("R_Sigma_over_R_s") == 1.0,
        "minimal_throat_ready": bool(mpla.get("minimal_throat_ready")),
        "Rs_absolute_scale_fixed": mass_charge["absolute_Rs_selected"],
        "mass_parameter_M_available": mass_charge["mass_charge_available"],
        "regular_timelike_hK_pipeline_compatible": not bool(
            eddington.get("R_const_throat_induced_metric_null")
        ),
        "null_sigma_formalism_active": False,
        "null_sigma_scale_selection_ready": null_scale["null_scale_selection_ready"],
    }
    return {
        "status": "janus-z2-sigma-schwarzschild-pt-bridge-scale-gate",
        "active_core": "Z2_tunnel_Sigma",
        "candidate_relation": "R_Sigma = R_s = 2*G*M/c^2",
        "local_result": {
            "R_Sigma_over_R_s": mpla.get("R_Sigma_over_R_s"),
            "absolute_scale_symbol": mpla.get("local_certificate", {}).get(
                "absolute_scale_symbol"
            ),
            "attractive_block_degenerate_at_Rs": signed.get(
                "attractive_block_degenerate_at_Rs"
            ),
            "bulk_TR_block_regular_at_Rs": eddington.get("bulk_TR_block_regular_at_Rs"),
            "R_const_throat_induced_metric_null": eddington.get(
                "R_const_throat_induced_metric_null"
            ),
        },
        "null_scale_gate": {
            "status": null_scale["status"],
            "scale_selection_ready": null_scale["null_scale_selection_ready"],
            "blocked_by": null_scale["blocked_by"],
        },
        "mass_charge_to_Rs": {
            "status": mass_charge["status"],
            "mass_charge_available": mass_charge["mass_charge_available"],
            "absolute_Rs_selected": mass_charge["absolute_Rs_selected"],
            "next_required": mass_charge["next_required"],
        },
        "closure": closure,
        "absolute_RSigma_from_schwarzschild_bridge_ready": all(closure.values()),
        "interpretation": (
            "The Schwarzschild/PT bridge fixes the dimensionless relation "
            "R_Sigma/R_s=1, but R_s still requires a mass/charge M. In the "
            "Eddington/PT version the R=R_s throat is null, so it does not feed "
            "the current regular h_ab,K_ab Sigma pipeline without switching to a "
            "null-boundary formalism."
        ),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "forbidden_shortcuts": [
            "do_not_set_Rs_to_one_as_physical_length",
            "do_not_use_null_Rs_throat_in_regular_hK_pipeline",
            "do_not_choose_M_by_observation_or_fit",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Schwarzschild PT Bridge Scale Gate",
        "",
        payload["interpretation"],
        "",
        f"Candidate relation: `{payload['candidate_relation']}`",
        f"Absolute R_Sigma ready: `{payload['absolute_RSigma_from_schwarzschild_bridge_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

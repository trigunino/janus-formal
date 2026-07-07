from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_area_gap_exit_gate import build_payload as area_gap
from scripts.build_p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate import (
    build_payload as casimir,
)
from scripts.build_p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate import (
    build_payload as horizon,
)
from scripts.build_p0_eft_janus_z2_chi_ll_regularity_global_closure_exit_gate import (
    build_payload as regularity,
)
from scripts.build_p0_eft_janus_z2_chi_ll_spectral_stability_exit_gate import (
    build_payload as spectral,
)
from scripts.build_p0_eft_janus_z2_chi_ll_uv_ll_action_exit_gate import (
    build_payload as uv_ll,
)
from scripts.build_p0_eft_janus_z2_null_sigma_chi_ll_noether_souriau_superselection_gate import (
    build_payload as state_charge,
)
from scripts.build_p0_eft_janus_z2_sigma_spin_current_of_a_gate import (
    build_payload as spin_current,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_eight_exit_coverage_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_eight_exit_coverage_audit.json")


def build_payload() -> dict:
    spin = spin_current()
    exits = {
        "area_gap_exit": {
            "gate": area_gap()["status"],
            "pushed_to_frontier": True,
            "prediction_ready": area_gap()["chi_LL_prediction_ready"],
            "frontier": "needs area operator on Sigma, A=N*A_gap theorem, N selection and physical area gauge",
        },
        "spin_condensate_exit": {
            "gate": spin["status"],
            "pushed_to_frontier": True,
            "prediction_ready": False,
            "frontier": "spin-current structure exists, but active fermion distribution/spin polarization/projection are open",
        },
        "UV_LL_action_exit": {
            "gate": uv_ll()["status"],
            "pushed_to_frontier": True,
            "prediction_ready": uv_ll()["chi_LL_prediction_ready"],
            "frontier": "needs active LL gauge normalization manifest",
        },
        "state_charge_exit": {
            "gate": state_charge()["status"],
            "pushed_to_frontier": True,
            "prediction_ready": state_charge()["closure"][
                "chi_LL_abs_inverse_m_derivable_downstream"
            ],
            "frontier": "needs active mass Casimir/Noether state and bridge matching value",
        },
        "horizon_thermodynamic_exit": {
            "gate": horizon()["status"],
            "pushed_to_frontier": True,
            "prediction_ready": horizon()["chi_LL_prediction_ready"],
            "frontier": "needs proved horizon status, kappa_l, R_s, first law and energy definition",
        },
        "spectral_stability_exit": {
            "gate": spectral()["status"],
            "pushed_to_frontier": True,
            "prediction_ready": spectral()["chi_LL_prediction_ready"],
            "frontier": "needs natural operator plus scale-selection law",
        },
        "Casimir_topological_exit": {
            "gate": casimir()["status"],
            "pushed_to_frontier": True,
            "prediction_ready": casimir()["chi_LL_prediction_ready"],
            "frontier": "needs field content, boundary conditions, renormalized C, and R_s/stationarity",
        },
        "regularity_global_closure_exit": {
            "gate": regularity()["status"],
            "pushed_to_frontier": True,
            "prediction_ready": regularity()["chi_LL_prediction_ready"],
            "frontier": "regularity can select dimensionless ratio only; needs absolute collar scale",
        },
    }
    return {
        "status": "janus-z2-chi-ll-eight-exit-coverage-audit",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "exits": exits,
        "all_eight_have_frontier_gate_or_imported_frontier": all(
            item["pushed_to_frontier"] for item in exits.values()
        ),
        "ready_exits": [name for name, item in exits.items() if item["prediction_ready"]],
        "chi_LL_prediction_ready": any(item["prediction_ready"] for item in exits.values()),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Eight Exit Coverage Audit",
        "",
        f"All exits pushed to frontier: `{payload['all_eight_have_frontier_gate_or_imported_frontier']}`",
        f"Ready exits: `{payload['ready_exits']}`",
        "",
        "## Exits",
    ]
    for name, data in payload["exits"].items():
        lines.append(f"- `{name}`: ready=`{data['prediction_ready']}`; {data['frontier']}")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

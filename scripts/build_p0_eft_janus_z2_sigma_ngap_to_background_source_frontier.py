from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_discrete_family_propagation import (
    build_payload as discrete_family,
)
from scripts.build_p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate import (
    build_payload as casimir,
)
from scripts.build_p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate import (
    build_payload as horizon,
)
from scripts.build_p0_eft_janus_z2_null_sigma_chi_ll_noether_souriau_superselection_gate import (
    build_payload as souriau,
)
from scripts.build_p0_eft_janus_z2_sigma_action_to_flrw_source_audit import (
    build_payload as action_to_flrw,
)


PT67_BOUNDARY_PATH = Path("outputs/active_z2_sigma/boundary_projection_charge_from_pt67_theta.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_ngap_to_background_source_frontier.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_ngap_to_background_source_frontier.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _pt67_boundary_status() -> dict[str, Any]:
    data = _read(PT67_BOUNDARY_PATH)
    return {
        "ready": bool(data.get("projected_positive_Friedmann_source_available")),
        "positive_friedmann_source_available": bool(
            data.get("projected_positive_Friedmann_source_available")
        ),
        "reason": data.get(
            "interpretation",
            "PT67 boundary projection manifest missing or does not provide source.",
        ),
    }


def _channel_statuses() -> dict[str, Any]:
    cas = casimir()
    hor = horizon()
    sou = souriau()
    action = action_to_flrw()
    return {
        "admitted_action_variation": {
            "kind": "current Janus/Z2/Sigma action variation",
            "ready": action["E_Z2Sigma_a2_ready"],
            "can_emit_E_Z2Sigma_of_a": action["E_Z2Sigma_a2_ready"],
            "rho_Sigma_status": action["rho_Sigma_status"],
            "blocked_by": []
            if action["E_Z2Sigma_a2_ready"]
            else ["current_admitted_action_variation_emits_zero_rho_Sigma"],
        },
        "regular_PT67_boundary_charge": {
            "kind": "boundary_Hamiltonian_source",
            "ready": _pt67_boundary_status()["ready"],
            "can_emit_E_Z2Sigma_of_a": False,
            "status": _pt67_boundary_status(),
        },
        "casimir_topological_source": {
            "kind": "rho_Casimir=C/R_s^4",
            "ready": cas["casimir_exit_prediction_ready"],
            "can_emit_E_Z2Sigma_of_a": cas["casimir_exit_prediction_ready"],
            "blocked_by": cas["blocked_by"],
            "note": "Would be N_gap-dependent through R_s, but needs field content, boundary conditions, C, and radius/stationarity.",
        },
        "horizon_PT_first_law_source": {
            "kind": "horizon energy / first law",
            "ready": hor["horizon_thermodynamic_exit_ready"],
            "can_emit_E_Z2Sigma_of_a": hor["horizon_thermodynamic_exit_ready"],
            "blocked_by": hor["blocked_by"],
            "note": "Would be N_gap-dependent through R_s if Sigma/PT horizon status and kappa normalization were derived.",
        },
        "noether_souriau_state_source": {
            "kind": "global charge / superselection state",
            "ready": sou["souriau_superselection_selects_chi_LL_now"],
            "can_emit_E_Z2Sigma_of_a": False,
            "blocked_by": sou["next_required"],
            "note": "Can label a state charge, but does not currently emit a background density or E(a).",
        },
        "LL_bridge_tension_source": {
            "kind": "chi_LL / bridge mass relation",
            "ready": False,
            "can_emit_E_Z2Sigma_of_a": False,
            "blocked_by": ["no derived map from bridge throat tension to homogeneous Friedmann source"],
            "note": "The discrete family gives chi_LL and M_bridge per sector; this is not yet a cosmological background density.",
        },
    }


def build_payload() -> dict[str, Any]:
    family = discrete_family()
    channels = _channel_statuses()
    source_channels_ready = [
        name for name, row in channels.items() if row["ready"] and row["can_emit_E_Z2Sigma_of_a"]
    ]
    sector_rows = []
    for sector in family["sector_table"]:
        sector_rows.append(
            {
                "N_gap": sector["N_gap"],
                "R_s_m": sector["R_s_m"],
                "chi_LL_abs_inverse_m": sector["chi_LL_abs_inverse_m"],
                "M_bridge_kg": sector["M_bridge_kg"],
                "available_throat_quantities_only": True,
                "background_source_available": bool(source_channels_ready),
            }
        )
    ready = family["discrete_family_propagation_ready"] and bool(source_channels_ready)
    return {
        "status": "janus-z2-sigma-ngap-to-background-source-frontier",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Tests whether fixed N_gap sectors can be promoted from throat data "
            "(R_s, chi_LL, M_bridge) to a homogeneous background source "
            "E_Z2Sigma(a)^2. No observation or continuous fit is used."
        ),
        "discrete_family_ready": family["discrete_family_propagation_ready"],
        "channels": channels,
        "source_channels_ready": source_channels_ready,
        "sector_rows": sector_rows,
        "N_gap_to_background_source_ready": ready,
        "sector_to_observable_map_derived": ready,
        "DESI_BAO_trial_unblocked": ready,
        "missing_effective_primitives": []
        if ready
        else [
            "E_Z2Sigma(a)^2",
            "H_Z2Sigma(z)",
            "D_M_Z2Sigma(z)",
            "D_H_Z2Sigma(z)",
            "D_V_Z2Sigma(z)",
            "r_d_or_sound_ruler_map",
        ],
        "current_verdict": (
            "N_gap currently reaches throat-sector quantities only. It does not "
            "yet reach DESI/Planck/KiDS observables because no active channel "
            "emits a derived homogeneous Friedmann source."
        ),
        "forbidden_shortcuts": [
            "treat_M_bridge_as_total_cosmic_density_without_volume_map",
            "use_old_Holst_or_Z4_background_scores_as_Z2Sigma_map",
            "fit_R_s_or_N_gap_to_DESI",
            "invent_Casimir_coefficient_or_horizon_kappa",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma N_gap To Background Source Frontier",
        "",
        payload["physical_statement"],
        "",
        f"N_gap to background source ready: `{payload['N_gap_to_background_source_ready']}`",
        f"DESI BAO trial unblocked: `{payload['DESI_BAO_trial_unblocked']}`",
        f"Ready channels: `{payload['source_channels_ready']}`",
        "",
        "## Channels",
    ]
    for name, channel in payload["channels"].items():
        lines.append(
            f"- `{name}`: ready=`{channel['ready']}`, "
            f"can_emit_E=`{channel['can_emit_E_Z2Sigma_of_a']}`"
        )
    lines.extend(["", "## Missing Effective Primitives"])
    lines.extend(f"- `{item}`" for item in payload["missing_effective_primitives"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))

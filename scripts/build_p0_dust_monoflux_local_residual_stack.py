from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_cold_vlasov_dust_preservation_probe import (
    build_payload as build_cold_vlasov,
)
from scripts.build_p0_connection_difference_cuu_identity import (
    build_payload as build_connection_identity,
)
from scripts.build_p0_dlogb4vol_jacobian_lapse_slice_identity_target import (
    build_payload as build_dlogb_identity,
)
from scripts.build_p0_dust_monoflux_cuu_conditional_closure import (
    build_payload as build_cuu_closure,
)
from scripts.build_p0_falpha_from_jacobian_tetrad_identity_target import (
    build_payload as build_falpha_identity,
)
from scripts.build_p0_pulled_particle_action_cuu_derivation import (
    build_payload as build_particle_cuu,
)
from scripts.build_p0_shared_phi_j_source_selection_gate import (
    build_payload as build_shared_phi_j,
)


REPORT_PATH = Path("outputs/reports/p0_dust_monoflux_local_residual_stack.md")
JSON_PATH = Path("outputs/reports/p0_dust_monoflux_local_residual_stack.json")


def build_payload() -> dict:
    cold = build_cold_vlasov()
    conn = build_connection_identity()
    dlogb = build_dlogb_identity()
    cuu = build_cuu_closure()
    falpha = build_falpha_identity()
    particle = build_particle_cuu()
    shared = build_shared_phi_j()
    local_rows = [
        {
            "row": "cold_dust_branch",
            "requires": "p=0 and Pi=0 on a monoflux Vlasov sheet before shell crossing",
            "closed": bool(cold["dust_branch_closed_conditionally"]),
        },
        {
            "row": "particle_geodesic_action",
            "requires": "particle action gives geodesic/connection-force skeleton",
            "closed": bool(
                particle["particle_geodesic_variation_closed"]
                and particle["cold_dust_lift_closed"]
            ),
        },
        {
            "row": "connection_difference_cuu",
            "requires": "C=Gamma_receiver-Gamma_source gives signed C(u,u)",
            "closed": bool(conn["cross_pullback_algebra_closed"]),
        },
        {
            "row": "projected_cuu_substitution",
            "requires": "hE-rho hCuu vanishes after the dust substitution",
            "closed": bool(cuu["conditional_cuu_closure"]),
        },
        {
            "row": "dlogb4vol_product_identity",
            "requires": "B4vol decomposes into Jacobian/lapse/slice factors",
            "closed": bool(dlogb["identity_numeric_closes"]),
        },
        {
            "row": "falpha_dl_identity",
            "requires": "D L computed from J and tetrad derivatives",
            "closed": bool(falpha["dl_identity_numeric_closes"]),
        },
    ]
    source_rows = [
        {
            "row": "shared_phi_j_source_selection",
            "requires": "one Janus-selected phi/J shared by Cuu, Falpha and B4vol",
            "closed": bool(shared["shared_source_selected_phi_j_closed"]),
        },
        {
            "row": "source_selected_measure",
            "requires": "B4vol measure selected by Janus source identity",
            "closed": bool(dlogb["source_selected_measure_found"]),
        },
        {
            "row": "source_selected_jacobian",
            "requires": "J=dphi selected by Janus source identity",
            "closed": bool(falpha["source_selected_jacobian_found"]),
        },
        {
            "row": "dynamic_phi_l_selection",
            "requires": "Janus action/source dynamically selects phi/L",
            "closed": bool(shared["dynamic_phi_l_selection_closed"]),
        },
    ]
    local_stack_closed = all(row["closed"] for row in local_rows)
    source_stack_closed = all(row["closed"] for row in source_rows)
    return {
        "description": "Local conditional residual stack for the cold monoflux dust branch.",
        "status": "dust-monoflux-local-stack-closed-source-stack-open",
        "local_rows": local_rows,
        "source_rows": source_rows,
        "local_conditional_stack_closed": local_stack_closed,
        "source_derived_stack_closed": source_stack_closed,
        "conditional_residual_algebra_ready": bool(local_stack_closed),
        "r_plus_r_minus_source_closed": False,
        "dust_monoflux_only": True,
        "multistream_forbidden": True,
        "pressure_pi_excluded": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "forbidden_promotions": [
            "do not promote this local stack to source-derived Janus closure",
            "do not use it after shell crossing or multistreaming",
            "do not extend it to pressure/Pi",
            "do not use it as a lensing or sigma8 normalization",
        ],
        "verdict": (
            "The cold monoflux dust residual algebra is locally assembled. The remaining "
            "blocker is no longer the Cuu sign or dust algebra; it is Janus source selection "
            "of one shared phi/J/L and B4vol measure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dust Monoflux Local Residual Stack",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Local conditional stack closed: {payload['local_conditional_stack_closed']}",
        f"Source-derived stack closed: {payload['source_derived_stack_closed']}",
        f"Conditional residual algebra ready: {payload['conditional_residual_algebra_ready']}",
        f"R plus/R minus source closed: {payload['r_plus_r_minus_source_closed']}",
        f"Dust monoflux only: {payload['dust_monoflux_only']}",
        f"Multistream forbidden: {payload['multistream_forbidden']}",
        f"Pressure/Pi excluded: {payload['pressure_pi_excluded']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Local Rows",
        "",
        "| row | requires | closed |",
        "|---|---|---:|",
    ]
    for row in payload["local_rows"]:
        lines.append(f"| {row['row']} | {row['requires']} | {row['closed']} |")
    lines.extend(["", "## Source Rows", "", "| row | requires | closed |", "|---|---|---:|"])
    for row in payload["source_rows"]:
        lines.append(f"| {row['row']} | {row['requires']} | {row['closed']} |")
    lines.extend(["", "## Forbidden Promotions", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_promotions"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

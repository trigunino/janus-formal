from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_same_l_spin_connection_transport_identity_gate import (
    build_payload as build_spin_connection_identity,
)


REPORT_PATH = Path("outputs/reports/p0_same_l_dl_residual_closure_ledger.md")
JSON_PATH = Path("outputs/reports/p0_same_l_dl_residual_closure_ledger.json")


def build_payload() -> dict:
    spin_connection_identity = build_spin_connection_identity()
    ledger = [
        {
            "obligation": "same_l_for_k_and_qcross",
            "required_identity": "one L_minus_to_plus induces K_plus/K_minus and optical Q_cross",
            "source_derived": False,
            "closed": False,
        },
        {
            "obligation": "lorentz_tetrad_compatibility",
            "required_identity": "L^T eta L=eta with compatible plus/minus tetrads",
            "source_derived": False,
            "closed": False,
        },
        {
            "obligation": "dl_identity",
            "required_identity": "D_alpha L=partial_alpha L+omega_s,alpha L-L omega_o,alpha, then Janus source-selects L/Omega",
            "source_derived": False,
            "closed": bool(
                spin_connection_identity["covariant_dl_identity_closed"]
                and spin_connection_identity["source_selected_l"]
            ),
        },
        {
            "obligation": "dlogb_identity",
            "required_identity": "D log B_4vol cancels measure terms in both residuals",
            "source_derived": False,
            "closed": False,
        },
        {
            "obligation": "r_plus_substitution",
            "required_identity": "substituted K_plus terms give R_plus=0",
            "source_derived": False,
            "closed": False,
        },
        {
            "obligation": "r_minus_substitution",
            "required_identity": "substituted K_minus terms give R_minus=0",
            "source_derived": False,
            "closed": False,
        },
    ]
    blockers = [
        "D_alpha L spin-connection identity is algebraic but L/Omega are not source-selected",
        "global Lorentz/tetrad compatibility is not proved",
        "same L for K/Q_cross is targeted but not derived",
        "R_plus/R_minus closure is conditional only",
        "pressure/Pi extension remains open",
    ]
    existing_surfaces = [
        "p0_l_k_qcross_consistency_target",
        "bianchi_lorentz_residual_reduction",
        "bianchi_l_map_source_equations_target",
        "p0_dl_lorentz_generator_obstruction",
        "p0_dl_dlogb_identity_targets",
        "bianchi_conditional_closure_theorem",
        "p0_transport_branch_closure_obligations",
    ]
    return {
        "description": "Ledger for the same-L, D L, D log B, and residual closure obligations.",
        "status": "closure-ledger-open",
        "ledger": ledger,
        "blockers": blockers,
        "existing_surfaces": existing_surfaces,
        "spin_connection_identity_artifact": "p0_same_l_spin_connection_transport_identity_gate",
        "spin_connection_identity_algebra_closed": bool(
            spin_connection_identity["covariant_dl_identity_closed"]
        ),
        "spin_connection_identity_source_selected": bool(spin_connection_identity["source_selected_l"]),
        "same_l_closed": False,
        "dl_closed": False,
        "dlogb_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This ledger localizes the remaining L/DL residual proof obligations. "
            "It records no closure until source-derived identities substitute into both residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Same-L DL Residual Closure Ledger",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Spin-connection identity artifact: `{payload['spin_connection_identity_artifact']}`",
        f"Spin-connection identity algebra closed: {payload['spin_connection_identity_algebra_closed']}",
        f"Spin-connection identity source selected: {payload['spin_connection_identity_source_selected']}",
        f"Same L closed: {payload['same_l_closed']}",
        f"DL closed: {payload['dl_closed']}",
        f"DlogB closed: {payload['dlogb_closed']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Ledger",
        "",
        "| obligation | required identity | source derived | closed |",
        "|---|---|---|---|",
    ]
    for row in payload["ledger"]:
        lines.append(
            f"| {row['obligation']} | {row['required_identity']} | "
            f"{row['source_derived']} | {row['closed']} |"
        )
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Existing Surfaces", ""])
    lines.extend(f"- `{item}`" for item in payload["existing_surfaces"])
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

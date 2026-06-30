from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_dl_source_law_traceability_gate import build_payload as build_dl_trace
from scripts.build_p0_l_k_qcross_consistency_target import build_payload as build_l_k_qcross
from scripts.build_p0_same_l_dl_residual_closure_ledger import build_payload as build_same_l_ledger
from scripts.build_p0_same_l_spin_connection_transport_identity_gate import (
    build_payload as build_spin_connection_identity,
)


REPORT_PATH = Path("outputs/reports/p0_source_derived_same_l_dl_residual_closure_target.md")
JSON_PATH = Path("outputs/reports/p0_source_derived_same_l_dl_residual_closure_target.json")


def build_payload() -> dict:
    ledger = build_same_l_ledger()
    trace = build_dl_trace()
    l_k_qcross = build_l_k_qcross()
    spin_connection_identity = build_spin_connection_identity()
    target_rows = [
        {
            "id": "SLDL-1",
            "obligation": "same_l_for_k_qcross_kinetics",
            "source_requirement": "one Janus-derived Lorentz L used for K, Q_cross, and kinetic projection",
            "current_anchor": "p0_same_l_dl_residual_closure_ledger",
            "source_derived": ledger["same_l_closed"],
            "closed": False,
        },
        {
            "id": "SLDL-2",
            "obligation": "dl_source_law",
            "source_requirement": "D_alpha L=partial_alpha L+omega_s,alpha L-L omega_o,alpha, then Janus source-selects L/Omega",
            "current_anchor": "p0_dl_source_law_traceability_gate",
            "source_derived": trace["source_derived_dl_law_found"],
            "closed": False,
        },
        {
            "id": "SLDL-3",
            "obligation": "lorentz_tetrad_compatibility",
            "source_requirement": "L^T eta L=eta with accepted plus/minus tetrads",
            "current_anchor": "p0_l_k_qcross_consistency_target",
            "source_derived": l_k_qcross["lorentz_tetrad_compatibility_proved"],
            "closed": False,
        },
        {
            "id": "SLDL-4",
            "obligation": "r_plus_substitution",
            "source_requirement": "same L and D L substituted into K_plus gives R_plus=0",
            "current_anchor": "p0_same_l_dl_residual_closure_ledger",
            "source_derived": ledger["r_plus_closed"],
            "closed": False,
        },
        {
            "id": "SLDL-5",
            "obligation": "r_minus_substitution",
            "source_requirement": "mirror same L and D L substituted into K_minus gives R_minus=0",
            "current_anchor": "p0_same_l_dl_residual_closure_ledger",
            "source_derived": ledger["r_minus_closed"],
            "closed": False,
        },
    ]
    forbidden_shortcuts = [
        "no raw L_geom promotion without Lorentz/tetrad proof",
        "no separate L for K and Q_cross",
        "no fitted observer boost",
        "no R_plus/R_minus closure by Q_det or Q_cross scalar absorption",
    ]
    return {
        "description": "Source-derived target for same-L, D L, and residual closure.",
        "status": "source-derived-same-l-dl-closure-target-open",
        "depends_on": [
            "p0_same_l_dl_residual_closure_ledger",
            "p0_dl_source_law_traceability_gate",
            "p0_same_l_spin_connection_transport_identity_gate",
            "p0_l_k_qcross_consistency_target",
            "p0_janus_source_residual_closure_obligation_matrix",
        ],
        "spin_connection_identity_artifact": "p0_same_l_spin_connection_transport_identity_gate",
        "spin_connection_identity_algebra_closed": bool(
            spin_connection_identity["covariant_dl_identity_closed"]
        ),
        "spin_connection_identity_source_selected": bool(spin_connection_identity["source_selected_l"]),
        "target_rows": target_rows,
        "forbidden_shortcuts": forbidden_shortcuts,
        "source_derived": all(row["source_derived"] for row in target_rows),
        "same_l_closed": False,
        "dl_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is the source-derived acceptance target for same-L/DL residual closure. "
            "It remains open until one Janus-derived L/DL structure closes both residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Derived Same-L DL Residual Closure Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source-derived: {payload['source_derived']}",
        f"Spin-connection identity artifact: `{payload['spin_connection_identity_artifact']}`",
        f"Spin-connection identity algebra closed: {payload['spin_connection_identity_algebra_closed']}",
        f"Spin-connection identity source selected: {payload['spin_connection_identity_source_selected']}",
        f"Same L closed: {payload['same_l_closed']}",
        f"DL closed: {payload['dl_closed']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Target Rows",
        "",
        "| id | obligation | source-derived | closed | requirement |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["target_rows"]:
        lines.append(
            f"| {row['id']} | {row['obligation']} | {row['source_derived']} | "
            f"{row['closed']} | {row['source_requirement']} |"
        )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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

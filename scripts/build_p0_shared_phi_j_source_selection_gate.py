from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_cuu_inverse_map_integrability_target import build_payload as build_cuu
from scripts.build_p0_dlogb4vol_jacobian_lapse_slice_identity_target import (
    build_payload as build_dlogb,
)
from scripts.build_p0_falpha_from_jacobian_tetrad_identity_target import (
    build_payload as build_falpha,
)
from scripts.build_p0_dynamic_phi_l_selection_mirror_closure import (
    build_payload as build_dynamic_selection,
)
from scripts.build_p0_integrability_first_phi_l_selection import (
    build_payload as build_integrability_route,
)
from scripts.build_p0_phi_scouple_source_or_axiom_decision import (
    build_payload as build_phi_scouple_decision,
)
from scripts.build_p0_phi_j_l_underselection_probe import build_payload as build_underselection


REPORT_PATH = Path("outputs/reports/p0_shared_phi_j_source_selection_gate.md")
JSON_PATH = Path("outputs/reports/p0_shared_phi_j_source_selection_gate.json")


def build_payload() -> dict:
    cuu = build_cuu()
    dlogb = build_dlogb()
    falpha = build_falpha()
    dynamic = build_dynamic_selection()
    integrability = build_integrability_route()
    phi_decision = build_phi_scouple_decision()
    underselection = build_underselection()
    rows = [
        {
            "consumer": "Cuu",
            "requires": "same invertible phi/L with J=dphi and mirror inverse",
            "local_identity_ready": bool(cuu["jacobian_curl_numeric_probe_available"]),
            "source_selected": bool(cuu["integrability_closed"]),
        },
        {
            "consumer": "F_alpha",
            "requires": "same J=e_plus L e_minus used to compute D L",
            "local_identity_ready": bool(falpha["dl_identity_numeric_closes"]),
            "source_selected": bool(falpha["source_selected_jacobian_found"]),
        },
        {
            "consumer": "B_4vol",
            "requires": "same J_phi in B4vol lapse/slice measure",
            "local_identity_ready": bool(dlogb["identity_numeric_closes"]),
            "source_selected": bool(dlogb["source_selected_measure_found"]),
        },
    ]
    forbidden = [
        "do not use one phi/J for Cuu and another for B4vol",
        "do not use one L/J for F_alpha and another for Q_cross/K transport",
        "do not close source residuals from locally valid identities without Janus source selection",
        "do not replace shared phi/J selection by Q_det or Q_cross normalization",
    ]
    selection_obligations = [
        {
            "name": "mirror_inverse",
            "required": "one inverse phi/L pair mirrors plus and minus sectors",
            "closed": bool(dynamic["mirror_inverse_consistency_closed"]),
        },
        {
            "name": "integrability_route",
            "required": "dust-image curl/Frobenius route is source-compatible and no-fit",
            "closed": bool(
                integrability["source_compatible"]
                and not integrability["uses_s_couple_selection"]
            ),
        },
        {
            "name": "dynamic_source_action",
            "required": "Janus source/action selects phi/J without new fitted normalization",
            "closed": bool(dynamic["dynamic_phi_l_selection_closed"]),
        },
        {
            "name": "underselection_resolved",
            "required": "local admissible phi/J/L family is reduced to one source-selected map",
            "closed": bool(underselection["unique_phi_j_l_selected"]),
        },
        {
            "name": "phi_scouple_source",
            "required": "Phi/Phi_bar or S_couple is source-derived, or explicit axiom is adopted",
            "closed": bool(
                phi_decision["decision"]["source_derived_phi_or_scouple_found"]
                or phi_decision["decision"]["axiom_adopted"]
            ),
        },
    ]
    return {
        "description": "Gate requiring one Janus-selected phi/J map shared by Cuu, F_alpha and B4vol.",
        "status": "shared-phi-j-source-selection-gate-open",
        "depends_on": [
            "p0_cuu_inverse_map_integrability_target",
            "p0_falpha_from_jacobian_tetrad_identity_target",
            "p0_dlogb4vol_jacobian_lapse_slice_identity_target",
            "p0_phi_j_l_underselection_probe",
        ],
        "rows": rows,
        "selection_obligations": selection_obligations,
        "forbidden_shortcuts": forbidden,
        "all_local_identities_ready": all(row["local_identity_ready"] for row in rows),
        "mirror_inverse_consistency_closed": bool(dynamic["mirror_inverse_consistency_closed"]),
        "integrability_route_source_compatible": bool(integrability["source_compatible"]),
        "dynamic_phi_l_selection_closed": bool(dynamic["dynamic_phi_l_selection_closed"]),
        "underselection_probe_available": True,
        "local_underselection_proved": bool(underselection["underselection_proved_for_family"]),
        "unique_phi_j_l_selected": bool(underselection["unique_phi_j_l_selected"]),
        "phi_scouple_source_or_axiom_closed": bool(selection_obligations[-1]["closed"]),
        "requires_new_axiom_or_source_action": bool(dynamic["requires_new_axiom_or_source_action"]),
        "all_consumers_source_selected": all(row["source_selected"] for row in rows),
        "shared_source_selected_phi_j_closed": all(row["closed"] for row in selection_obligations)
        and all(row["source_selected"] for row in rows),
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The local identities are ready, but the common physical map is not. "
            "Janus must select one integrable phi/J shared by Cuu, F_alpha and B4vol."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Shared Phi/J Source Selection Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All local identities ready: {payload['all_local_identities_ready']}",
        f"Local underselection proved: {payload['local_underselection_proved']}",
        f"Unique phi/J/L selected: {payload['unique_phi_j_l_selected']}",
        f"All consumers source-selected: {payload['all_consumers_source_selected']}",
        f"Shared source-selected phi/J closed: {payload['shared_source_selected_phi_j_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Consumers",
        "",
        "| consumer | requires | local identity ready | source selected |",
        "|---|---|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['consumer']} | {row['requires']} | "
            f"{row['local_identity_ready']} | {row['source_selected']} |"
        )
    lines.extend(
        [
            "",
            "## Selection Obligations",
            "",
            "| name | required | closed |",
            "|---|---|---:|",
        ]
    )
    for row in payload["selection_obligations"]:
        lines.append(f"| {row['name']} | {row['required']} | {row['closed']} |")
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

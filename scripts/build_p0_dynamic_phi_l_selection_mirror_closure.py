from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dynamic_phi_l_selection_mirror_closure.md")
JSON_PATH = Path("outputs/reports/p0_dynamic_phi_l_selection_mirror_closure.json")


def build_payload() -> dict:
    selection_rows = [
        {
            "row": "source_action",
            "claim": "M15/M30 provide coupled field equations but no unique phi/L variational action",
            "closed": False,
        },
        {
            "row": "explicit_stueckelberg_action",
            "claim": "delta phi and delta L define formal map equations once Phi/Phi_bar are chosen",
            "closed": "formal-only",
        },
        {
            "row": "phi_potential_selection",
            "claim": "Phi/Phi_bar remain constrained by mirror/no-fit/sign rules but not uniquely fixed",
            "closed": False,
        },
        {
            "row": "dynamic_selection",
            "claim": "Janus does not yet source-select a unique phi/L from the available action/source rows",
            "closed": False,
        },
    ]
    mirror_rows = [
        {
            "row": "inverse_constraint",
            "identity": "phi_plus_to_minus o phi_minus_to_plus = id and phi_minus_to_plus o phi_plus_to_minus = id",
            "closed": True,
        },
        {
            "row": "tetrad_inverse",
            "identity": "L_plus_to_minus = L_minus_to_plus^{-1}",
            "closed": True,
        },
        {
            "row": "determinant_inverse",
            "identity": "B_4vol_minus_to_plus * B_4vol_plus_to_minus = 1",
            "closed": True,
        },
        {
            "row": "cuu_mirror",
            "identity": "C_minus-plus is the inverse-map mirror of C_plus-minus",
            "closed": True,
        },
    ]
    consequences = [
        "mirror plus/minus consistency is closed when the inverse-map constraint is part of the action",
        "single cross-dust hE=rho hCuu survives in both mirrored sectors",
        "dynamic phi/L selection remains open unless Phi/S_couple is source-derived or accepted as new axiom",
        "full R_plus=R_minus closure remains blocked by dynamic selection and non-dust matter",
    ]
    return {
        "description": "Decision artifact for dynamic phi/L selection and plus/minus mirror closure.",
        "status": "mirror-closed-dynamic-selection-open",
        "selection_rows": selection_rows,
        "mirror_rows": mirror_rows,
        "consequences": consequences,
        "dynamic_phi_l_selection_closed": False,
        "mirror_inverse_consistency_closed": True,
        "single_cross_dust_mirror_cuu_closed": True,
        "requires_new_axiom_or_source_action": True,
        "full_two_sector_bianchi_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The mirror row can be closed by the inverse phi/L constraint already present "
            "in the Stueckelberg action test. The dynamic selection row cannot be closed "
            "from current Janus sources because Phi/S_couple is not uniquely supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dynamic Phi/L Selection Mirror Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Mirror inverse consistency closed: {payload['mirror_inverse_consistency_closed']}",
        f"Single cross-dust mirror Cuu closed: {payload['single_cross_dust_mirror_cuu_closed']}",
        f"Requires new axiom or source action: {payload['requires_new_axiom_or_source_action']}",
        f"Full two-sector Bianchi closed: {payload['full_two_sector_bianchi_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Selection Rows",
        "",
    ]
    for row in payload["selection_rows"]:
        lines.append(f"- {row['row']}: {row['claim']} (closed={row['closed']})")
    lines.extend(["", "## Mirror Rows", ""])
    for row in payload["mirror_rows"]:
        lines.append(f"- {row['row']}: `{row['identity']}` (closed={row['closed']})")
    lines.extend(["", "## Consequences", ""])
    lines.extend(f"- {item}" for item in payload["consequences"])
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

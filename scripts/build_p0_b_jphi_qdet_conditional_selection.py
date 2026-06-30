from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_b_jphi_qdet_conditional_selection.md")
JSON_PATH = Path("outputs/reports/p0_b_jphi_qdet_conditional_selection.json")


def build_payload() -> dict:
    selection_rule = [
        {
            "context": "field_equation_residual",
            "selected": "field_equation_4volume_source",
            "reason": "coupled field equations use sqrt(-g_self) divergences, so pulled source density must carry the 4-volume ratio B_4vol",
        },
        {
            "context": "dust_flux_continuity",
            "selected": "dust_flux_3volume_auxiliary_only",
            "reason": "3-volume/Jacobian may express transported dust flux, but must be lifted back to 4-volume before R_plus/R_minus substitution",
        },
        {
            "context": "effective_density_bookkeeping",
            "selected": "rho_eff_allowed_after_B_absorption",
            "reason": "rho_eff is only B_4vol rho_to after convention lock; Q_det must not be multiplied again",
        },
    ]
    consequences = [
        "Q_det is the density/volume map B_4vol for field-equation source terms",
        "Q_cross remains optical projection and cannot absorb B/J_phi terms",
        "lapse terms stay present; dust 3-volume cannot replace B_4vol in field residuals",
        "D_receiver(B_4vol rho_to u_to)=0 remains a proof obligation",
        "R_plus/R_minus are not closed by selecting the branch",
    ]
    rejected_for_field_residual = [
        "slice_dust_flux_source as final field-equation source",
        "raw (a_minus/a_plus)^3 or ^4 as lensing amplitude",
        "effective_density_source with second Q_det multiplication",
    ]
    return {
        "description": "Conditional B/J_phi/Q_det branch selection for field-equation residual work.",
        "status": "conditional-selection-open",
        "selected_field_residual_branch": "field_equation_4volume_source",
        "source_traceability_closed": False,
        "lapse_slice_closed": False,
        "effective_density_continuity_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "selection_rule": selection_rule,
        "consequences": consequences,
        "rejected_for_field_residual": rejected_for_field_residual,
        "verdict": (
            "For field-equation residual substitution, the only admissible conditional "
            "branch is B_4vol. This is a convention selection for the proof path, not "
            "a source-derived closure or lensing normalization."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 B/J_phi/Q_det Conditional Selection",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selected field residual branch: {payload['selected_field_residual_branch']}",
        f"Source traceability closed: {payload['source_traceability_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Selection Rule",
        "",
    ]
    for row in payload["selection_rule"]:
        lines.append(f"- {row['context']}: {row['selected']}")
        lines.append(f"  - reason: {row['reason']}")
    lines.extend(["", "## Consequences", ""])
    lines.extend(f"- {item}" for item in payload["consequences"])
    lines.extend(["", "## Rejected For Field Residual", ""])
    lines.extend(f"- {item}" for item in payload["rejected_for_field_residual"])
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

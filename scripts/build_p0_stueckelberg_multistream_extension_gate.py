from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_multistream_extension_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_multistream_extension_gate.json")


def build_payload() -> dict:
    options = [
        {
            "name": "stop_at_caustic",
            "description": "diagnostic branch ends when transverse Jacobian vanishes",
            "admissible": True,
            "prediction_scope": "pre-caustic only",
        },
        {
            "name": "sheet_sum",
            "description": "represent post-caustic dust as a finite sum of single-stream sheets",
            "admissible": "conditional",
            "prediction_scope": "requires each sheet to keep its own phi/L and weight",
        },
        {
            "name": "kinetic_distribution",
            "description": "replace dust congruence by f(x,p) phase-space transport",
            "admissible": "future-extension",
            "prediction_scope": "requires new transport derivation",
        },
        {
            "name": "smooth_caustic_fit",
            "description": "regularize caustic by tuned smoothing length",
            "admissible": False,
            "prediction_scope": "forbidden fit",
        },
    ]
    required_for_sheet_sum = [
        "no independent sheet-specific Q_cross normalization",
        "weights come from transported density/volume, not observational fit",
        "mirror inverse relation is sheet-wise",
        "same-L rule applies per sheet and in the summed optical quantity",
    ]
    decision = {
        "post_caustic_closure_available": False,
        "pre_caustic_diagnostic_allowed": True,
        "sheet_sum_is_next_nonfit_extension": True,
        "kinetic_extension_needed_for_full_structure": True,
        "prediction_ready": False,
        "reason": (
            "After caustics, a single-valued dust map is invalid. The non-fit path is "
            "either stop diagnostics at caustic, or move to sheet-summed/kinetic transport "
            "with the same no-independent-normalization rules."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_multistream_extension_gate",
        "status": "post-caustic-extension-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "options": options,
        "required_for_sheet_sum": required_for_sheet_sum,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Multistream Extension Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Options",
    ]
    for row in payload["options"]:
        lines.append(f"- {row['name']}: {row['description']}")
        lines.append(f"  - admissible: {row['admissible']}")
        lines.append(f"  - prediction scope: {row['prediction_scope']}")
    lines.extend(["", "## Required For Sheet Sum"])
    lines.extend(f"- {item}" for item in payload["required_for_sheet_sum"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Post-caustic closure available: {decision['post_caustic_closure_available']}",
            f"Pre-caustic diagnostic allowed: {decision['pre_caustic_diagnostic_allowed']}",
            f"Sheet sum is next nonfit extension: {decision['sheet_sum_is_next_nonfit_extension']}",
            f"Kinetic extension needed for full structure: {decision['kinetic_extension_needed_for_full_structure']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")

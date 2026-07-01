from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_postfix_validity_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_postfix_validity_audit.json")
REPORTS_DIR = Path("outputs/reports")

INVALIDATED = {
    "p0_eft_primordial_theta_scan_debug.json",
    "p0_eft_primordial_theta_scan_decision.json",
}

POST_FIX_VALID = {
    "p0_eft_coherent_primordial_immirzi_planck_gate.json",
    "p0_eft_coherent_immirzi_activation_profile_scan.json",
    "p0_eft_coherent_immirzi_tt_shape_delta.json",
    "p0_eft_coherent_immirzi_planck_channel_delta.json",
    "p0_eft_holst_full_stress_tensor_patch.json",
    "p0_eft_immirzi_consistent_patch_planck_gate.json",
    "p0_eft_immirzi_geff_planck_gate.json",
    "p0_eft_immirzi_patch_mini_scan.json",
    "p0_eft_primordial_mode_bug_invalidation.json",
    "p0_eft_primordial_theta_scan.json",
    "p0_eft_predrag_background_only_geff_scan.json",
    "p0_eft_screened_rd_cmb_projection_scan.json",
    "p0_eft_screened_geff_camb_gate.json",
    "p0_eft_two_mode_primordial_scan.json",
}


def classify(path: Path) -> str:
    if path.name in INVALIDATED:
        return "invalidated_pre_fix"
    if path.name in POST_FIX_VALID:
        return "post_fix_valid"
    text = path.read_text(encoding="utf-8", errors="ignore")
    if any(token in text for token in ["c_sound", "c_opacity", "c_geff", "c_immirzi", "janus_primordial_mode"]):
        return "review_before_citation"
    return "not_primordial_mode_dependent"


def build_payload() -> dict:
    rows = []
    for path in sorted(REPORTS_DIR.glob("p0_eft_*.json")):
        status = classify(path)
        if status != "not_primordial_mode_dependent":
            rows.append({"report": path.name, "validity": status})
    return {
        "description": "CMB report validity audit after fixing janus_primordial_mode zero-amplitude bug.",
        "status": "cmb-postfix-validity-audit-run",
        "invalidated_count": sum(1 for row in rows if row["validity"] == "invalidated_pre_fix"),
        "post_fix_valid_count": sum(1 for row in rows if row["validity"] == "post_fix_valid"),
        "review_count": sum(1 for row in rows if row["validity"] == "review_before_citation"),
        "rows": rows,
        "rule": "Do not cite invalidated_pre_fix reports as physical CMB verdicts. Use post_fix_valid reports for current conclusions.",
        "full_cosmology_prediction_ready_no_fit": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Post-Fix Validity Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Invalidated: `{payload['invalidated_count']}`",
        f"Post-fix valid: `{payload['post_fix_valid_count']}`",
        f"Review before citation: `{payload['review_count']}`",
        "",
        payload["rule"],
        "",
        "| report | validity |",
        "|---|---|",
    ]
    lines.extend(f"| `{row['report']}` | `{row['validity']}` |" for row in payload["rows"])
    return "\n".join(lines) + "\n"


def write_reports() -> dict:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

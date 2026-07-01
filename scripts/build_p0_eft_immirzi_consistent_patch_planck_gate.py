from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_consistent_patch_planck_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_consistent_patch_planck_gate.json")
POSTFIX_GATE_PATH = Path("outputs/reports/p0_eft_coherent_primordial_immirzi_planck_gate.json")
PATCH_PATH = Path("outputs/reports/p0_eft_holst_full_stress_tensor_patch.json")


def build_payload() -> dict:
    gate = json.loads(POSTFIX_GATE_PATH.read_text(encoding="utf-8"))
    patch = json.loads(PATCH_PATH.read_text(encoding="utf-8"))
    return {
        "description": "Post-fix audit replacing the invalidated static consistent-Immirzi Planck gate.",
        "status": "immirzi-consistent-patch-planck-gate-postfix-superseded",
        "pre_fix_static_result_invalidated": True,
        "postfix_replacement_report": str(POSTFIX_GATE_PATH),
        "full_stress_tensor_patch_report": str(PATCH_PATH),
        "patch_complete": patch["stress_tensor_patch_complete"],
        "postfix_gate": {
            "chi2_CMB": gate["chi2_CMB"],
            "delta_chi2_CMB": gate["delta_chi2_CMB"],
            "delta_chi2_highl": gate["delta_chi2_highl"],
            "delta_chi2_lensing": gate["delta_chi2_lensing"],
            "planck_delta_accepted": gate["planck_delta_accepted"],
        },
        "improves_over_background_only": False,
        "improves_over_neutral_fixed_branch": False,
        "planck_accepted": gate["planck_delta_accepted"],
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "Do not cite the pre-fix static gate. Use post-fix coherent stress tensor results only.",
    }


def render_markdown(payload: dict) -> str:
    t = payload["postfix_gate"]
    return "\n".join(
        [
            "# P0 EFT Immirzi Consistent Patch Planck Gate",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Planck accepted: {payload['planck_accepted']}",
            f"Pre-fix static result invalidated: {payload['pre_fix_static_result_invalidated']}",
            f"Patch complete: {payload['patch_complete']}",
            "",
            "## Post-fix Replacement",
            "",
            f"- chi2 CMB: {t['chi2_CMB']:.6g}",
            f"- delta chi2 CMB: {t['delta_chi2_CMB']:.6g}",
            f"- delta highl: {t['delta_chi2_highl']:.6g}",
            f"- delta lensing: {t['delta_chi2_lensing']:.6g}",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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

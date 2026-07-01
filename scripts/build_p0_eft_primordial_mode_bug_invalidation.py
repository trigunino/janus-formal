from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_primordial_mode_bug_invalidation.md")
JSON_PATH = Path("outputs/reports/p0_eft_primordial_mode_bug_invalidation.json")

AFFECTED = [
    "p0_eft_immirzi_geff_planck_gate",
    "p0_eft_immirzi_patch_mini_scan",
    "p0_eft_immirzi_consistent_patch_planck_gate",
    "p0_eft_coherent_primordial_immirzi_planck_gate_before_primordial_mode_fix",
    "p0_eft_coherent_immirzi_tt_shape_delta_before_subprocess_fix",
]


def build_payload() -> dict:
    return {
        "description": "Invalidation marker for CMB runs executed while janus_primordial_mode carried an internal zero amplitude.",
        "status": "primordial-mode-zero-amplitude-runs-invalidated",
        "bug": "janus_primordial_mode returned amp * window with amp = 0, making activation-based hooks silent.",
        "fixed_rule": "janus_primordial_mode is now a pure window; amplitudes live only in explicit hook coefficients.",
        "affected_reports": AFFECTED,
        "must_rerun_before_citation": True,
        "full_cosmology_prediction_ready_no_fit": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Primordial Mode Bug Invalidation",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Must rerun before citation: `{payload['must_rerun_before_citation']}`",
        "",
        "## Affected",
        "",
    ]
    lines.extend(f"- `{name}`" for name in payload["affected_reports"])
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

from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.kink_source import kink_jump_amplitude, kink_source_status

try:
    from scripts.build_kids1000_janus_holst_kink_lensing_target import build_payload as build_kink_target
    from scripts.build_p0_eft_kink_source_closure_audit import build_payload as build_closure_audit
except ModuleNotFoundError:
    from build_kids1000_janus_holst_kink_lensing_target import build_payload as build_kink_target
    from build_p0_eft_kink_source_closure_audit import build_payload as build_closure_audit


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_kink_source_target.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_kink_source_target.json")


def build_payload() -> dict:
    target = build_kink_target()
    closure = build_closure_audit()
    k = np.asarray([0.1, 1.0])
    a = np.asarray([2.0 / 3.0, 1.0])
    delta = np.asarray([1.0e-3, 2.0e-3])
    sample = kink_jump_amplitude(
        k,
        a,
        delta,
        coefficient=lambda kk, aa: 0.25 + 0.0 * kk + 0.0 * aa,
        alpha=lambda aa: 0.5 + 0.0 * aa,
        provenance="symbolic_scaffold",
    )
    status = kink_source_status(
        skink_coefficient_derived=False,
        alpha_janus_derived=False,
        provenance="symbolic_scaffold",
    )
    return {
        "description": "No-fit target for the source term feeding the Janus-Holst kink growth jump.",
        "status": "kink-source-target-open",
        "parent_target_status": target["status"],
        "solver_status": "kink-growth-solver-scaffold-not-predictive",
        "closure_audit_status": closure["status"],
        "jump_operator": "Delta(d delta / d ln a) = S_kink(k,a_sigma) * alpha_Janus(a_sigma) * delta(a_sigma)",
        "source_status": status,
        "sample_diagnostic_only": {
            "k": k.tolist(),
            "a": a.tolist(),
            "delta": delta.tolist(),
            "coefficient": 0.25,
            "alpha": 0.5,
            "jump_amplitude": sample.tolist(),
        },
        "open_locks": {
            "skink_coefficient_derived": closure["theorem_status"]["skink_coefficient_derived"],
            "alpha_Janus_derived": closure["theorem_status"]["alpha_Janus_derived"],
        },
        "source_closure_blockers": closure["open_blockers"],
        "forbidden_shortcuts": target["forbidden_shortcuts"]
        + [
            "derive S_kink from KiDS pair residuals",
            "derive alpha_Janus(a) from bin-2 photo-z shift",
            "promote symbolic_scaffold to prediction provenance",
        ],
        "uses_kids_residuals": False,
        "uses_bin_shift": False,
        "uses_bin_factors": False,
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Kink Source Target",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Parent target status: `{payload['parent_target_status']}`",
        f"Solver status: `{payload['solver_status']}`",
        f"Closure audit status: `{payload['closure_audit_status']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        f"Operator: `{payload['jump_operator']}`",
        "",
        "## Open Locks",
        "",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["open_locks"].items())
    lines.extend(["", "## Source Status", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["source_status"].items())
    lines.extend(["", "## Source Closure Blockers", ""])
    lines.extend(f"- {item}" for item in payload["source_closure_blockers"])
    lines.extend(["", "## Diagnostic Sample", ""])
    sample = payload["sample_diagnostic_only"]
    lines.extend(
        [
            f"- coefficient: `{sample['coefficient']}`",
            f"- alpha: `{sample['alpha']}`",
            f"- jump amplitude: `{sample['jump_amplitude']}`",
        ]
    )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.append("")
    return "\n".join(lines)


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

from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_kids1000_janus_holst_kernel_residual_audit import build_payload as build_residual_payload
except ModuleNotFoundError:
    from build_kids1000_janus_holst_kernel_residual_audit import build_payload as build_residual_payload


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_kernel_closure_decision.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_kernel_closure_decision.json")


def build_payload() -> dict:
    residual = build_residual_payload()
    best = min(residual["variants"], key=lambda row: row["chi2"])
    return {
        "description": "Decision record for the KiDS-1000 Janus-Holst kernel diagnostics.",
        "status": "diagnostic-kernel-candidate-frozen",
        "frozen_diagnostic_candidate": {
            "eta_holst": 0.0,
            "spectral_index": 0.5,
            "kernel_variant": best["kernel_variant"],
            "chi2_per_dof": best["chi2_per_dof"],
        },
        "promotion_decision": "do-not-promote-to-prediction",
        "reason": (
            "The angular_lens variant improves the residuals but leaves the 2-3 tomographic "
            "pair as the dominant failure and still relies on KiDS-inspected eta/tilt plus fitted amplitude."
        ),
        "next_required_closures": [
            "source-derived eta/value-slip kernel",
            "source-derived primordial amplitude",
            "nonlinear and baryon policy fixed before residual inspection",
            "IA policy fixed before residual inspection",
        ],
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    candidate = payload["frozen_diagnostic_candidate"]
    lines = [
        "# KiDS-1000 Janus-Holst Kernel Closure Decision",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Decision: `{payload['promotion_decision']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Frozen Diagnostic Candidate",
        "",
        f"- eta_holst: `{candidate['eta_holst']}`",
        f"- spectral_index: `{candidate['spectral_index']}`",
        f"- kernel_variant: `{candidate['kernel_variant']}`",
        f"- chi2/dof: `{candidate['chi2_per_dof']:.6g}`",
        "",
        "## Reason",
        "",
        payload["reason"],
        "",
        "## Next Required Closures",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["next_required_closures"])
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

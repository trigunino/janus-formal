from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_kids1000_janus_holst_bin_factor_audit import build_payload as build_bin_factor_payload
    from scripts.build_kids1000_janus_holst_kernel_closure_decision import build_payload as build_kernel_decision
    from scripts.build_kids1000_janus_holst_pair_amplitude_audit import build_payload as build_pair_amplitude_payload
    from scripts.build_kids1000_janus_holst_per_bin_nz_shift_audit import build_payload as build_per_bin_shift_payload
    from scripts.build_kids1000_physics_closure_gates import build_payload as build_gate_payload
except ModuleNotFoundError:
    from build_kids1000_janus_holst_bin_factor_audit import build_payload as build_bin_factor_payload
    from build_kids1000_janus_holst_kernel_closure_decision import build_payload as build_kernel_decision
    from build_kids1000_janus_holst_pair_amplitude_audit import build_payload as build_pair_amplitude_payload
    from build_kids1000_janus_holst_per_bin_nz_shift_audit import build_payload as build_per_bin_shift_payload
    from build_kids1000_physics_closure_gates import build_payload as build_gate_payload


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_no_fit_boundary.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_no_fit_boundary.json")


def build_payload() -> dict:
    kernel = build_kernel_decision()
    gates = build_gate_payload()
    pair_amplitude = build_pair_amplitude_payload()
    bin_factor = build_bin_factor_payload()
    per_bin_shift = build_per_bin_shift_payload(bins=[2], shifts=[0.0, 0.05, 0.10, 0.15, 0.20])
    candidate = kernel["frozen_diagnostic_candidate"]
    return {
        "description": "No-fit boundary for KiDS-1000 Janus-Holst diagnostics.",
        "status": "kids1000-janus-holst-no-fit-boundary-active",
        "frozen_diagnostic_candidate": candidate,
        "dominant_failure": {
            "pair": "2-3",
            "pair23_amplitude_global_ratio": pair_amplitude["pair23_ratio"],
            "bin_factor_highest": max(bin_factor["bin_factors"], key=bin_factor["bin_factors"].get),
            "best_posthoc_shifted_bin": per_bin_shift["best_shifted_bin"],
            "best_posthoc_delta_z": per_bin_shift["best_delta_z"],
            "best_posthoc_chi2_per_dof": per_bin_shift["best_chi2_per_dof"],
        },
        "allowed_uses": [
            "debug Janus lensing observable map",
            "prioritize value-slip/kernel derivation",
            "compare future source-derived predictions against frozen diagnostics",
        ],
        "forbidden_uses": [
            "use KiDS best amplitude as Janus primordial amplitude",
            "use eta_holst=0 because it improves KiDS",
            "use spectral_index=0.5 because it improves KiDS",
            "use angular_lens as default prediction kernel before tensor closure",
            "use bin-2 delta_z shift as photo-z nuisance",
            "use bin factors as calibration, IA, or baryon nuisance",
        ],
        "open_gates": [row for row in gates["gates"] if not row["closed"]],
        "prediction_ready": False,
        "prediction_claim_allowed": False,
    }


def render_markdown(payload: dict) -> str:
    candidate = payload["frozen_diagnostic_candidate"]
    failure = payload["dominant_failure"]
    lines = [
        "# KiDS-1000 Janus-Holst No-Fit Boundary",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        f"Prediction claim allowed: `{payload['prediction_claim_allowed']}`",
        "",
        "## Frozen Diagnostic Candidate",
        "",
        f"- eta_holst: `{candidate['eta_holst']}`",
        f"- spectral_index: `{candidate['spectral_index']}`",
        f"- kernel_variant: `{candidate['kernel_variant']}`",
        f"- diagnostic chi2/dof: `{candidate['chi2_per_dof']:.6g}`",
        "",
        "## Dominant Failure",
        "",
        f"- pair: `{failure['pair']}`",
        f"- pair 2-3 amplitude/global ratio: `{failure['pair23_amplitude_global_ratio']:.6g}`",
        f"- highest fitted bin factor: `{failure['bin_factor_highest']}`",
        f"- best posthoc shifted bin: `{failure['best_posthoc_shifted_bin']}`",
        f"- best posthoc delta_z: `{failure['best_posthoc_delta_z']}`",
        f"- best posthoc chi2/dof: `{failure['best_posthoc_chi2_per_dof']:.6g}`",
        "",
        "## Allowed Uses",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["allowed_uses"])
    lines.extend(["", "## Forbidden Uses", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_uses"])
    lines.extend(["", "## Open Gates", ""])
    lines.extend(f"- {row['gate']}: {row['required']}" for row in payload["open_gates"])
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

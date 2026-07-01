from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_janus_holst_pair_amplitude_audit import build_payload as build_pair_payload
except ModuleNotFoundError:
    from build_kids1000_janus_holst_pair_amplitude_audit import build_payload as build_pair_payload


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_bin_factor_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_bin_factor_audit.json")


def fit_bin_factors(pair_rows: list[dict], bin_count: int = 5) -> tuple[list[float], list[dict], float]:
    design = []
    target = []
    for row in pair_rows:
        ratio = float(row["pair_to_global_amplitude_ratio"])
        if ratio <= 0.0:
            continue
        vector = np.zeros(bin_count, dtype=float)
        vector[int(row["bin1"]) - 1] += 1.0
        vector[int(row["bin2"]) - 1] += 1.0
        design.append(vector)
        target.append(np.log(ratio))
    coeffs, *_ = np.linalg.lstsq(np.asarray(design), np.asarray(target), rcond=None)
    factors = np.exp(coeffs)
    residual_rows = []
    for row in pair_rows:
        predicted = float(factors[int(row["bin1"]) - 1] * factors[int(row["bin2"]) - 1])
        observed = float(row["pair_to_global_amplitude_ratio"])
        residual_rows.append(
            {
                "bin1": int(row["bin1"]),
                "bin2": int(row["bin2"]),
                "observed_ratio": observed,
                "factorized_ratio": predicted,
                "log_residual": float(np.log(observed / predicted)),
            }
        )
    rms = float(np.sqrt(np.mean([row["log_residual"] ** 2 for row in residual_rows])))
    return [float(value) for value in factors], residual_rows, rms


def build_payload() -> dict:
    pair_payload = build_pair_payload()
    factors, residual_rows, log_rms = fit_bin_factors(pair_payload["pair_rows"])
    return {
        "description": "Tomographic bin-factor diagnostic for KiDS-1000 Janus-Holst pair amplitudes.",
        "status": "diagnostic-bin-factor-audit-computed",
        "kernel_variant": pair_payload["kernel_variant"],
        "bin_factors": {f"bin{index + 1}": value for index, value in enumerate(factors)},
        "pair_factorization_log_rms": log_rms,
        "residual_rows": residual_rows,
        "prediction_ready": False,
        "boundary": (
            "These bin factors are fitted to pair amplitudes after inspecting KiDS. They are "
            "a localization diagnostic only, not a photo-z, IA, or calibration model."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Bin-Factor Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Kernel variant: `{payload['kernel_variant']}`",
        f"Pair factorization log RMS: `{payload['pair_factorization_log_rms']:.6g}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Bin Factors",
        "",
    ]
    lines.extend(f"- {key}: `{value:.6g}`" for key, value in payload["bin_factors"].items())
    lines.extend(
        [
            "",
            "## Largest Factorization Residuals",
            "",
            "| bin1 | bin2 | observed ratio | factorized ratio | log residual |",
            "|---:|---:|---:|---:|---:|",
        ]
    )
    for row in sorted(payload["residual_rows"], key=lambda item: abs(item["log_residual"]), reverse=True)[:8]:
        lines.append(
            f"| {row['bin1']} | {row['bin2']} | {row['observed_ratio']:.6g} | "
            f"{row['factorized_ratio']:.6g} | {row['log_residual']:.6g} |"
        )
    lines.extend(["", payload["boundary"], ""])
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

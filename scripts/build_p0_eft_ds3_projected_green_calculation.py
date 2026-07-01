from __future__ import annotations

from pathlib import Path
import json
import math

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_eft_ds3_projected_green_calculation.md")
JSON_PATH = Path("outputs/reports/p0_eft_ds3_projected_green_calculation.json")


def s3_spectral_response(
    *,
    h: float = 1.0,
    mass_gap_over_h2: float = 1.5,
    cutoff_epsilon: float = 0.05,
    l_max: int = 512,
    remove_zero_mode: bool = True,
) -> float:
    if h <= 0.0 or mass_gap_over_h2 <= 0.0 or cutoff_epsilon <= 0.0 or l_max < 2:
        raise ValueError("invalid spectral response parameters")
    start = 1 if remove_zero_mode else 0
    ell = np.arange(start, l_max + 1, dtype=float)
    degeneracy = (ell + 1.0) ** 2
    eigenvalue = ell * (ell + 2.0) * h * h
    heat_cutoff = np.exp(-cutoff_epsilon * (ell + 1.0) ** 2)
    volume = 2.0 * math.pi**2 / h**3
    response = np.sum(degeneracy * heat_cutoff / (eigenvalue + mass_gap_over_h2 * h * h)) / volume
    return float(response)


def cutoff_scan() -> list[dict]:
    rows = []
    for epsilon in [0.2, 0.1, 0.05, 0.025, 0.0125]:
        response = s3_spectral_response(cutoff_epsilon=epsilon)
        rows.append(
            {
                "cutoff_epsilon": epsilon,
                "projected_response_over_H": response,
                "ratio_to_three_halves": response / 1.5,
            }
        )
    return rows


def build_payload() -> dict:
    rows = cutoff_scan()
    ratios = [row["ratio_to_three_halves"] for row in rows]
    return {
        "description": "Regulated S3 spectral Green calculation audit for the Janus-Holst value-slip target.",
        "status": "regulated-spectral-green-scheme-dependent",
        "operator": "O_Sigma = -Delta_S3 + M_eff^2, M_eff^2/H^2=3/2",
        "regularization": "heat-kernel cutoff exp[-epsilon(l+1)^2] with zero mode removed",
        "rows": rows,
        "target_response_over_H": 1.5,
        "scheme_dependent": (max(ratios) - min(ratios)) > 0.05,
        "green_kernel_equals_three_halves_H_proved": False,
        "value_slip_ready": False,
        "verdict": (
            "The regulated spectral response is finite only after a scheme choice and does not "
            "prove G_Neumann^Sigma=(3/2)H. A source-derived projection/renormalization rule is still required."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT dS3 Projected Green Calculation",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Operator: `{payload['operator']}`",
        f"Regularization: `{payload['regularization']}`",
        f"Target response/H: `{payload['target_response_over_H']}`",
        f"Scheme dependent: `{payload['scheme_dependent']}`",
        f"Green equals 3H/2 proved: `{payload['green_kernel_equals_three_halves_H_proved']}`",
        f"Value slip ready: `{payload['value_slip_ready']}`",
        "",
        "| cutoff epsilon | response/H | ratio to 3/2 |",
        "|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['cutoff_epsilon']:.6g} | {row['projected_response_over_H']:.6g} | "
            f"{row['ratio_to_three_halves']:.6g} |"
        )
    lines.extend(["", payload["verdict"], ""])
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

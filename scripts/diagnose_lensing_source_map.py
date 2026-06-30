from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.lensing import (
    positive_photon_lensing_contrast,
    positive_photon_lensing_potential_2d,
)


REPORT_PATH = Path("outputs/reports/lensing_source_map.md")
JSON_PATH = Path("outputs/reports/lensing_source_map.json")


def gaussian_bump(grid: int, center: tuple[float, float], width: float) -> np.ndarray:
    axis = (np.arange(grid) + 0.5) / grid
    xx, yy = np.meshgrid(axis, axis, indexing="ij")
    radius2 = (xx - center[0]) ** 2 + (yy - center[1]) ** 2
    return np.exp(-0.5 * radius2 / width**2)


def summarize_case(name: str, positive: np.ndarray, negative: np.ndarray) -> dict:
    contrast = positive_photon_lensing_contrast(positive, negative)
    potential = positive_photon_lensing_potential_2d(positive, negative, box_size=1.0)
    center = tuple(index // 2 for index in contrast.shape)
    return {
        "case": name,
        "center_lensing_contrast": float(contrast[center]),
        "min_lensing_contrast": float(np.min(contrast)),
        "max_lensing_contrast": float(np.max(contrast)),
        "center_potential": float(potential[center]),
        "min_potential": float(np.min(potential)),
        "max_potential": float(np.max(potential)),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid = 64
    bump = gaussian_bump(grid, center=(0.5, 0.5), width=0.08)
    positive = np.ones((grid, grid), dtype=float)
    negative_cluster = np.ones((grid, grid), dtype=float) + bump
    negative_hole = np.maximum(np.ones((grid, grid), dtype=float) - 0.8 * bump, 0.0)

    rows = [
        summarize_case("negative_cluster", positive, negative_cluster),
        summarize_case("negative_hole", positive, negative_hole),
    ]
    payload = {
        "description": "Weak-field positive-sector lensing source diagnostic.",
        "source_formula": "delta_lens_plus = ((rho_plus - rho_minus_abs) - mean(rho_plus - rho_minus_abs)) / mean(rho_plus + rho_minus_abs)",
        "rows": rows,
        "boundary": "Diagnostic Newtonian-limit source map only; not a relativistic shear/convergence prediction.",
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Source Map",
        "",
        "Weak-field source diagnostic for positive-energy photons.",
        "",
        "```text",
        payload["source_formula"],
        "```",
        "",
        "| case | center contrast | min contrast | max contrast | reading |",
        "|---|---:|---:|---:|---|",
    ]
    for row in rows:
        reading = (
            "negative-mass concentration gives negative/diverging source"
            if row["case"] == "negative_cluster"
            else "negative-mass hole gives positive lensing source"
        )
        lines.append(
            f"| {row['case']} | {row['center_lensing_contrast']:.6g} | "
            f"{row['min_lensing_contrast']:.6g} | {row['max_lensing_contrast']:.6g} | "
            f"{reading} |"
        )
    lines.extend(
        [
            "",
            f"JSON: `{JSON_PATH}`",
            "",
            "Boundary: diagnostic Newtonian-limit source map only; not a relativistic shear/convergence prediction.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()

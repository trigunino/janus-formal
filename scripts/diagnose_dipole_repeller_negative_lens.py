from __future__ import annotations

from pathlib import Path
import csv
import json

import numpy as np

from janus_lab.lensing import (
    negative_mass_sphere_annular_dimming_map,
    negative_mass_sphere_annular_dimming_profile,
    negative_mass_sphere_reduced_deflection_profile,
)


REPORT_PATH = Path("outputs/reports/dipole_repeller_negative_lens.md")
JSON_PATH = Path("outputs/reports/dipole_repeller_negative_lens.json")
CSV_PATH = Path("outputs/reports/dipole_repeller_negative_lens.csv")


def build_payload() -> dict:
    impact_over_radius = np.asarray([0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0])
    deflection = np.asarray(
        negative_mass_sphere_reduced_deflection_profile(
            impact_over_radius,
            sphere_radius=1.0,
        ),
        dtype=float,
    )
    dimming = np.asarray(
        negative_mass_sphere_annular_dimming_profile(
            impact_over_radius,
            sphere_radius=1.0,
        ),
        dtype=float,
    )
    grid = np.linspace(-2.0, 2.0, 65)
    xx, yy = np.meshgrid(grid, grid, indexing="ij")
    dimming_map = negative_mass_sphere_annular_dimming_map(
        xx,
        yy,
        sphere_radius=1.0,
    )
    center = dimming_map[dimming_map.shape[0] // 2, dimming_map.shape[1] // 2]
    radial_distance = np.sqrt(xx**2 + yy**2)
    ring_mask = np.abs(radial_distance - 1.0) <= (grid[1] - grid[0])
    max_index = int(np.argmax(dimming))
    return {
        "description": "Normalized dipole-repeller negative-lensing shape diagnostic.",
        "source": "X2025 technical book Sect. XI; X2026 source freshness audit keeps it as an observable target.",
        "status": "shape-diagnostic-not-survey-fit",
        "profile": [
            {
                "impact_over_radius": float(impact),
                "reduced_deflection": float(alpha),
                "relative_dimming": float(mu),
            }
            for impact, alpha, mu in zip(impact_over_radius, deflection, dimming)
        ],
        "checks": {
            "center_zero": bool(np.isclose(dimming[0], 0.0)),
            "maximum_at_surface": bool(np.isclose(impact_over_radius[max_index], 1.0)),
            "negative_deflection": bool(np.all(deflection[1:] < 0.0)),
            "external_decay": bool(dimming[-1] < dimming[-2] < dimming[max_index]),
            "map_center_zero": bool(np.isclose(center, 0.0)),
            "map_ring_is_bright": bool(float(np.mean(dimming_map[ring_mask])) > 0.95),
        },
        "map_summary": {
            "grid_size": int(dimming_map.shape[0]),
            "max_relative_dimming": float(np.max(dimming_map)),
            "mean_ring_relative_dimming": float(np.mean(dimming_map[ring_mask])),
            "center_relative_dimming": float(center),
        },
        "verdict": (
            "The normalized profile has the expected annular signature: no central "
            "dimming, maximum at the object radius, and exterior decay. Absolute "
            "amplitude still requires a mass/radius and optical normalization."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["impact_over_radius", "reduced_deflection", "relative_dimming"],
        )
        writer.writeheader()
        writer.writerows(payload["profile"])

    lines = [
        "# Dipole Repeller Negative Lens Diagnostic",
        "",
        payload["description"],
        "",
        f"Source: {payload['source']}",
        f"Status: {payload['status']}",
        "",
        "| b/R | reduced deflection | relative dimming |",
        "|---:|---:|---:|",
    ]
    for row in payload["profile"]:
        lines.append(
            f"| {row['impact_over_radius']:.2f} | {row['reduced_deflection']:.6g} | "
            f"{row['relative_dimming']:.6g} |"
        )
    lines.extend(["", "## Checks", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["checks"].items())
    lines.extend(["", "## Map Summary", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["map_summary"].items())
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
